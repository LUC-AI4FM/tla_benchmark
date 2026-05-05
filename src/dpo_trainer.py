from __future__ import annotations

import contextlib
import copy
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

import torch
from torch.optim import AdamW
from torch.utils.data import DataLoader, Dataset
from transformers import AutoModelForCausalLM, AutoTokenizer, get_linear_schedule_with_warmup

# peft 0.19.1 checks torch.distributed.tensor as an attribute but PyTorch 2.7
# doesn't expose it that way — import it explicitly so the attribute exists.
import torch.distributed.tensor as _dt
import torch.distributed as _dist
if not hasattr(_dist, "tensor"):
    _dist.tensor = _dt

from peft import get_peft_model, LoraConfig, TaskType

from utils import get_logger, outputs_dir, repo_root, save_json, load_json

logger = get_logger("dpo_trainer")


class PreferenceDataset(Dataset):
    def __init__(self, jsonl_path: str | Path, tokenizer, max_length: int = 2048):
        self.data = []
        with open(jsonl_path, "r") as f:
            for line in f:
                if line.strip():
                    self.data.append(json.loads(line))

        self.tokenizer = tokenizer
        self.max_length = max_length

    def __len__(self) -> int:
        return len(self.data)

    def __getitem__(self, idx: int) -> dict[str, Any]:
        item = self.data[idx]

        # Track prompt length to exclude prompt tokens from the DPO loss
        prompt_tokens = self.tokenizer(
            item["prompt"],
            max_length=self.max_length,
            truncation=True,
            return_tensors="pt",
        )
        prompt_len = prompt_tokens["input_ids"].shape[1]

        chosen_text = item["prompt"] + item["chosen"]
        rejected_text = item["prompt"] + item["rejected"]

        chosen_tokens = self.tokenizer(
            chosen_text,
            max_length=self.max_length,
            truncation=True,
            padding="max_length",
            return_tensors="pt",
        )
        rejected_tokens = self.tokenizer(
            rejected_text,
            max_length=self.max_length,
            truncation=True,
            padding="max_length",
            return_tensors="pt",
        )

        return {
            "chosen_input_ids": chosen_tokens["input_ids"].squeeze(0),
            "chosen_attention_mask": chosen_tokens["attention_mask"].squeeze(0),
            "rejected_input_ids": rejected_tokens["input_ids"].squeeze(0),
            "rejected_attention_mask": rejected_tokens["attention_mask"].squeeze(0),
            "prompt_len": torch.tensor(prompt_len, dtype=torch.long),
        }


class DPOTrainer:
    def __init__(
        self,
        model_name: str,
        output_dir: str | Path,
        beta: float = 0.1,
        learning_rate: float = 1e-4,
        num_epochs: int = 5,
        batch_size: int = 4,
        warmup_steps: int = 100,
        max_length: int = 2048,
        use_lora: bool = True,
        lora_rank: int = 16,
        lora_alpha: int = 32,
        lora_dropout: float = 0.05,
        wandb_project: str = "tla_bench",
        wandb_entity: str | None = None,
        wandb_run_name: str | None = None,
    ):
        self.model_name = model_name
        self.output_dir = Path(output_dir)
        self.beta = beta
        self.learning_rate = learning_rate
        self.num_epochs = num_epochs
        self.batch_size = batch_size
        self.warmup_steps = warmup_steps
        self.max_length = max_length
        self.use_lora = use_lora
        self.lora_rank = lora_rank
        self.lora_alpha = lora_alpha
        self.lora_dropout = lora_dropout
        self.wandb_project = wandb_project
        self.wandb_entity = wandb_entity
        self.wandb_run_name = wandb_run_name or f"dpo_{Path(model_name).name}"

        n_gpus = torch.cuda.device_count()
        self.device     = torch.device("cuda:0" if torch.cuda.is_available() else "cpu")
        # Reference model goes on GPU 1 when available so the two models don't
        # compete for the same device memory.  Falls back to GPU 0 / CPU.
        self.ref_device = torch.device("cuda:1" if n_gpus >= 2 else self.device)

        dtype = torch.float16 if torch.cuda.is_available() else torch.float32

        self.tokenizer = AutoTokenizer.from_pretrained(model_name, local_files_only=True)

        if self.tokenizer.pad_token is None:
            self.tokenizer.pad_token = self.tokenizer.eos_token

        # Policy model — will be fine-tuned with LoRA
        self.model = AutoModelForCausalLM.from_pretrained(
            model_name, torch_dtype=dtype, local_files_only=True
        ).to(self.device)

        # Reference model — loaded separately from disk (avoids deepcopy OOM on large models)
        # DPO requires comparing policy log-probs against a fixed reference to
        # prevent the policy from drifting too far (KL constraint).
        self.ref_model = AutoModelForCausalLM.from_pretrained(
            model_name, torch_dtype=dtype, local_files_only=True
        ).to(self.ref_device)
        for param in self.ref_model.parameters():
            param.requires_grad_(False)
        self.ref_model.eval()

        logger.info(
            "Models loaded | policy → %s | reference → %s | dtype=%s",
            self.device, self.ref_device, dtype,
        )

        if self.use_lora:
            self._apply_lora()

        self.output_dir.mkdir(parents=True, exist_ok=True)

    def _apply_lora(self) -> None:
        peft_config = LoraConfig(
            r=self.lora_rank,
            lora_alpha=self.lora_alpha,
            lora_dropout=self.lora_dropout,
            bias="none",
            task_type=TaskType.CAUSAL_LM,
            target_modules=["q_proj", "k_proj", "v_proj", "o_proj"],
        )
        self.model = get_peft_model(self.model, peft_config)
        trainable_params = sum(p.numel() for p in self.model.parameters() if p.requires_grad)
        total_params = sum(p.numel() for p in self.model.parameters())
        logger.info(
            "LoRA Applied | Trainable: %s / %s (%.2f%%)",
            f"{trainable_params:,}", f"{total_params:,}", 100 * trainable_params / total_params,
        )

    def _sequence_log_probs(
        self,
        logits: torch.Tensor,
        input_ids: torch.Tensor,
        attention_mask: torch.Tensor,
        prompt_len: torch.Tensor,
    ) -> torch.Tensor:
        """Compute mean per-token log probability of the completion (excluding prompt and padding)."""
        # Next-token prediction: logit at position i predicts token at position i+1
        shift_logits = logits[:, :-1, :]           # (batch, seq-1, vocab)
        shift_labels = input_ids[:, 1:]             # (batch, seq-1)
        shift_mask = attention_mask[:, 1:].float()  # (batch, seq-1)

        # Only score completion tokens, not prompt tokens
        batch_size, seq_len = shift_labels.shape
        positions = torch.arange(seq_len, device=logits.device).unsqueeze(0).expand(batch_size, -1)
        completion_mask = (positions >= (prompt_len.unsqueeze(1) - 1)).float()

        final_mask = shift_mask * completion_mask

        log_probs = torch.nn.functional.log_softmax(shift_logits, dim=-1)
        token_log_probs = log_probs.gather(2, shift_labels.unsqueeze(2)).squeeze(2)

        # Mean over completion tokens (clamp avoids div-by-zero on empty completions)
        seq_log_probs = (token_log_probs * final_mask).sum(dim=-1) / final_mask.sum(dim=-1).clamp(min=1)
        return seq_log_probs

    def _dpo_loss(
        self,
        policy_chosen_logps: torch.Tensor,
        policy_rejected_logps: torch.Tensor,
        ref_chosen_logps: torch.Tensor,
        ref_rejected_logps: torch.Tensor,
    ) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """Standard DPO loss (Rafailov et al. 2024).

        L = -E[log σ(β · (r_chosen - r_rejected))]
        where r = log π_θ(y|x) - log π_ref(y|x)
        """
        chosen_rewards = self.beta * (policy_chosen_logps - ref_chosen_logps)
        rejected_rewards = self.beta * (policy_rejected_logps - ref_rejected_logps)
        loss = -torch.nn.functional.logsigmoid(chosen_rewards - rejected_rewards).mean()
        return loss, chosen_rewards.detach().mean(), rejected_rewards.detach().mean()

    def _forward_pass(
        self,
        model: torch.nn.Module,
        batch: dict[str, torch.Tensor],
        no_grad: bool = False,
    ) -> tuple[torch.Tensor, torch.Tensor]:
        """Run model forward pass and return per-sequence log probabilities."""
        context = torch.no_grad() if no_grad else contextlib.nullcontext()

        # Determine which device this model lives on
        model_device = next(model.parameters()).device
        prompt_len = batch["prompt_len"].to(model_device)

        with context:
            chosen_outputs = model(
                input_ids=batch["chosen_input_ids"].to(model_device),
                attention_mask=batch["chosen_attention_mask"].to(model_device),
            )
            rejected_outputs = model(
                input_ids=batch["rejected_input_ids"].to(model_device),
                attention_mask=batch["rejected_attention_mask"].to(model_device),
            )

        chosen_logps = self._sequence_log_probs(
            chosen_outputs.logits,
            batch["chosen_input_ids"].to(model_device),
            batch["chosen_attention_mask"].to(model_device),
            prompt_len,
        )
        rejected_logps = self._sequence_log_probs(
            rejected_outputs.logits,
            batch["rejected_input_ids"].to(model_device),
            batch["rejected_attention_mask"].to(model_device),
            prompt_len,
        )

        # Always return log-probs on the policy device so DPO loss computation is consistent
        return chosen_logps.to(self.device), rejected_logps.to(self.device)

    def train(self, train_dataset_path: str | Path, eval_dataset_path: str | Path | None = None) -> dict[str, Any]:
        import wandb

        run = wandb.init(
            project=self.wandb_project,
            entity=self.wandb_entity,
            name=self.wandb_run_name,
            group="dpo_training",
            job_type="train",
            config={
                "model_name": self.model_name,
                "beta": self.beta,
                "learning_rate": self.learning_rate,
                "num_epochs": self.num_epochs,
                "batch_size": self.batch_size,
                "warmup_steps": self.warmup_steps,
                "max_length": self.max_length,
                "use_lora": self.use_lora,
                "lora_rank": self.lora_rank,
                "lora_alpha": self.lora_alpha,
                "lora_dropout": self.lora_dropout,
                "trainer": "dpo",
            },
        )

        try:
            dataset = PreferenceDataset(train_dataset_path, self.tokenizer, self.max_length)
            dataloader = DataLoader(dataset, batch_size=self.batch_size, shuffle=True)

            num_training_steps = len(dataloader) * self.num_epochs
            optimizer = AdamW(
                [p for p in self.model.parameters() if p.requires_grad],
                lr=self.learning_rate,
            )
            scheduler = get_linear_schedule_with_warmup(
                optimizer,
                num_warmup_steps=self.warmup_steps,
                num_training_steps=num_training_steps,
            )

            train_history: dict[str, Any] = {
                "epoch_losses": [],
                "batch_losses": [],
                "chosen_rewards": [],
                "rejected_rewards": [],
            }
            global_step = 0

            self.model.train()
            self.ref_model.eval()

            for epoch in range(self.num_epochs):
                epoch_loss = 0.0
                epoch_chosen_r = 0.0
                epoch_rejected_r = 0.0

                for batch_idx, batch in enumerate(dataloader):
                    # Policy forward pass — gradients must flow here
                    policy_chosen_logps, policy_rejected_logps = self._forward_pass(
                        self.model, batch, no_grad=False
                    )
                    # Reference forward pass — frozen, no gradients needed
                    ref_chosen_logps, ref_rejected_logps = self._forward_pass(
                        self.ref_model, batch, no_grad=True
                    )

                    loss, chosen_r, rejected_r = self._dpo_loss(
                        policy_chosen_logps, policy_rejected_logps,
                        ref_chosen_logps, ref_rejected_logps,
                    )

                    optimizer.zero_grad()
                    loss.backward()
                    torch.nn.utils.clip_grad_norm_(self.model.parameters(), max_norm=1.0)
                    optimizer.step()
                    scheduler.step()

                    loss_val = loss.item()
                    chosen_val = chosen_r.item()
                    rejected_val = rejected_r.item()

                    epoch_loss += loss_val
                    epoch_chosen_r += chosen_val
                    epoch_rejected_r += rejected_val
                    train_history["batch_losses"].append(loss_val)
                    train_history["chosen_rewards"].append(chosen_val)
                    train_history["rejected_rewards"].append(rejected_val)
                    global_step += 1

                    wandb.log({
                        "train/loss": loss_val,
                        "train/chosen_reward": chosen_val,
                        "train/rejected_reward": rejected_val,
                        "train/reward_margin": chosen_val - rejected_val,
                        "train/learning_rate": scheduler.get_last_lr()[0],
                    }, step=global_step)

                    if (batch_idx + 1) % 10 == 0:
                        logger.info(
                            "Epoch %d/%d Batch %d/%d Loss: %.4f | chosen_r: %.4f | rejected_r: %.4f",
                            epoch + 1, self.num_epochs, batch_idx + 1, len(dataloader),
                            loss_val, chosen_val, rejected_val,
                        )

                n_batches = len(dataloader)
                avg_epoch_loss = epoch_loss / n_batches
                train_history["epoch_losses"].append(avg_epoch_loss)

                wandb.log({
                    "train/epoch_loss": avg_epoch_loss,
                    "train/epoch_chosen_reward": epoch_chosen_r / n_batches,
                    "train/epoch_rejected_reward": epoch_rejected_r / n_batches,
                    "train/epoch_reward_margin": (epoch_chosen_r - epoch_rejected_r) / n_batches,
                    "epoch": epoch + 1,
                }, step=global_step)

                logger.info("Epoch %d/%d Average Loss: %.4f", epoch + 1, self.num_epochs, avg_epoch_loss)

            if eval_dataset_path and Path(eval_dataset_path).exists():
                eval_results = self.evaluate(eval_dataset_path)
                train_history["eval_results"] = eval_results
                wandb.log({
                    "eval/loss": eval_results["eval_loss"],
                    "eval/preference_accuracy": eval_results["preference_accuracy"],
                }, step=global_step)
                logger.info(
                    "Eval — loss: %.4f preference_accuracy: %.4f",
                    eval_results["eval_loss"], eval_results["preference_accuracy"],
                )

            wandb.summary.update({
                "final_train_loss": train_history["epoch_losses"][-1] if train_history["epoch_losses"] else None,
                "eval_preference_accuracy": train_history.get("eval_results", {}).get("preference_accuracy"),
                "model_name": self.model_name,
            })

        finally:
            run.finish()

        return train_history

    def evaluate(self, eval_dataset_path: str | Path) -> dict[str, Any]:
        dataset = PreferenceDataset(eval_dataset_path, self.tokenizer, self.max_length)
        dataloader = DataLoader(dataset, batch_size=self.batch_size, shuffle=False)

        self.model.eval()
        total_loss = 0.0
        total_preference_accuracy = 0.0

        for batch in dataloader:
            policy_chosen_logps, policy_rejected_logps = self._forward_pass(
                self.model, batch, no_grad=True
            )
            ref_chosen_logps, ref_rejected_logps = self._forward_pass(
                self.ref_model, batch, no_grad=True
            )

            loss, _, _ = self._dpo_loss(
                policy_chosen_logps, policy_rejected_logps,
                ref_chosen_logps, ref_rejected_logps,
            )

            correct = (policy_chosen_logps > policy_rejected_logps).float().mean()
            total_preference_accuracy += correct.item()
            total_loss += loss.item()

        num_batches = len(dataloader)
        return {
            "eval_loss": total_loss / num_batches if num_batches > 0 else 0.0,
            "preference_accuracy": total_preference_accuracy / num_batches if num_batches > 0 else 0.0,
        }

    def save_checkpoint(self, checkpoint_dir: str | Path | None = None) -> str:
        if checkpoint_dir is None:
            checkpoint_dir = self.output_dir / "final_model"

        checkpoint_dir = Path(checkpoint_dir)
        checkpoint_dir.mkdir(parents=True, exist_ok=True)

        self.model.save_pretrained(str(checkpoint_dir))
        self.tokenizer.save_pretrained(str(checkpoint_dir))

        logger.info("Model saved to: %s", checkpoint_dir)
        return str(checkpoint_dir)

    def load_checkpoint(self, checkpoint_dir: str | Path) -> None:
        self.model = AutoModelForCausalLM.from_pretrained(str(checkpoint_dir)).to(self.device)
        self.tokenizer = AutoTokenizer.from_pretrained(str(checkpoint_dir))
        logger.info("Model loaded from: %s", checkpoint_dir)


def train_dpo_model(
    base_model: str,
    train_dataset_path: str | Path,
    eval_dataset_path: str | Path | None = None,
    output_dir: str | Path | None = None,
    config: dict[str, Any] | None = None,
    wandb_project: str = "tla_bench",
    wandb_entity: str | None = None,
) -> dict[str, Any]:
    if output_dir is None:
        output_dir = outputs_dir() / "dpo_models"

    if config is None:
        config = {
            "beta": 0.1,
            "learning_rate": 1e-4,
            "num_epochs": 5,
            "batch_size": 4,
            "warmup_steps": 100,
            "max_length": 2048,
            "use_lora": True,
            "lora_rank": 16,
            "lora_alpha": 32,
            "lora_dropout": 0.05,
        }

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    trainer = DPOTrainer(
        model_name=base_model,
        output_dir=output_dir,
        beta=config.get("beta", 0.1),
        learning_rate=config.get("learning_rate", 1e-4),
        num_epochs=config.get("num_epochs", 5),
        batch_size=config.get("batch_size", 4),
        warmup_steps=config.get("warmup_steps", 100),
        max_length=config.get("max_length", 2048),
        use_lora=config.get("use_lora", True),
        lora_rank=config.get("lora_rank", 16),
        lora_alpha=config.get("lora_alpha", 32),
        lora_dropout=config.get("lora_dropout", 0.05),
        wandb_project=wandb_project,
        wandb_entity=wandb_entity,
    )

    logger.info("Starting DPO training with config: %s", config)
    train_history = trainer.train(train_dataset_path, eval_dataset_path)

    results = {
        "base_model": base_model,
        "config": config,
        "train_history": train_history,
    }

    if "eval_results" in train_history:
        results["eval_results"] = train_history["eval_results"]

    checkpoint_path = trainer.save_checkpoint()
    results["checkpoint_path"] = checkpoint_path

    results_file = output_dir / "training_results.json"
    save_json(results, results_file)
    logger.info("Training results saved to: %s", results_file)

    return results


def main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--base-model", required=True, help="Base model name or path")
    parser.add_argument("--train-dataset", required=True, help="Training dataset JSONL path")
    parser.add_argument("--eval-dataset", default=None, help="Evaluation dataset JSONL path")
    parser.add_argument("--output-dir", default=None, help="Output directory for model checkpoints")
    parser.add_argument("--beta", type=float, default=0.1, help="DPO beta parameter")
    parser.add_argument("--learning-rate", type=float, default=1e-4, help="Learning rate")
    parser.add_argument("--num-epochs", type=int, default=5, help="Number of training epochs")
    parser.add_argument("--batch-size", type=int, default=4, help="Batch size")
    parser.add_argument("--warmup-steps", type=int, default=100, help="Warmup steps")
    parser.add_argument("--max-length", type=int, default=2048, help="Max token length")
    parser.add_argument("--use-lora", action="store_true", default=True, help="Use LoRA adaptation (default: True)")
    parser.add_argument("--no-lora", action="store_true", help="Disable LoRA (full fine-tuning)")
    parser.add_argument("--lora-rank", type=int, default=16, help="LoRA rank (8-32 recommended)")
    parser.add_argument("--lora-alpha", type=int, default=32, help="LoRA alpha scaling")
    parser.add_argument("--lora-dropout", type=float, default=0.05, help="LoRA dropout")
    parser.add_argument("--wandb-project", default="tla_bench", help="W&B project name")
    parser.add_argument("--wandb-entity", default=None, help="W&B entity (team/user)")
    args = parser.parse_args()

    use_lora = not args.no_lora and args.use_lora

    config = {
        "beta": args.beta,
        "learning_rate": args.learning_rate,
        "num_epochs": args.num_epochs,
        "batch_size": args.batch_size,
        "warmup_steps": args.warmup_steps,
        "max_length": args.max_length,
        "use_lora": use_lora,
        "lora_rank": args.lora_rank,
        "lora_alpha": args.lora_alpha,
        "lora_dropout": args.lora_dropout,
    }

    train_dpo_model(
        base_model=args.base_model,
        train_dataset_path=args.train_dataset,
        eval_dataset_path=args.eval_dataset,
        output_dir=args.output_dir,
        config=config,
        wandb_project=args.wandb_project,
        wandb_entity=args.wandb_entity,
    )


if __name__ == "__main__":
    main()
