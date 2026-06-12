from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

import torch
from torch.optim import AdamW
from torch.utils.data import DataLoader, Dataset
from transformers import AutoModelForCausalLM, AutoTokenizer, get_linear_schedule_with_warmup
from peft import get_peft_model, LoraConfig, TaskType

from utils import data_dir, get_logger, load_json, load_text, outputs_dir, repo_root, save_json

logger = get_logger("sft_trainer")


# dataset

class SFTDataset(Dataset):
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
        prompt = item["prompt"]
        completion = item["completion"]

        # Tokenise prompt alone to find its length
        prompt_enc = self.tokenizer(
            prompt,
            max_length=self.max_length,
            truncation=True,
            return_tensors="pt",
        )
        prompt_len = prompt_enc["input_ids"].shape[1]

        # Full sequence: prompt + completion
        full_enc = self.tokenizer(
            prompt + completion,
            max_length=self.max_length,
            truncation=True,
            padding="max_length",
            return_tensors="pt",
        )

        input_ids = full_enc["input_ids"].squeeze(0)
        attention_mask = full_enc["attention_mask"].squeeze(0)

        # Labels: -100 for prompt tokens and padding so loss is only on completion
        labels = input_ids.clone()
        labels[:prompt_len] = -100
        labels[attention_mask == 0] = -100

        return {
            "input_ids": input_ids,
            "attention_mask": attention_mask,
            "labels": labels,
        }


# trainer

class SFTTrainer:
    def __init__(
        self,
        model_name: str,
        output_dir: str | Path,
        learning_rate: float = 2e-4,
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
        self.wandb_run_name = wandb_run_name or f"sft_{Path(model_name).name}"

        # pick the gpu with most free vram so sft can co-run with dpo on gpu 0
        if torch.cuda.is_available():
            free = [torch.cuda.mem_get_info(i)[0] for i in range(torch.cuda.device_count())]
            self.device = torch.device(f"cuda:{free.index(max(free))}")
        else:
            self.device = torch.device("cpu")

        dtype = torch.float16 if torch.cuda.is_available() else torch.float32
        self.tokenizer = AutoTokenizer.from_pretrained(model_name, local_files_only=True)

        if self.tokenizer.pad_token is None:
            self.tokenizer.pad_token = self.tokenizer.eos_token

        self.model = AutoModelForCausalLM.from_pretrained(
            model_name, torch_dtype=dtype, local_files_only=True
        ).to(self.device)

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
        trainable = sum(p.numel() for p in self.model.parameters() if p.requires_grad)
        total = sum(p.numel() for p in self.model.parameters())
        logger.info("lora applied: trainable=%d total=%d (%.2f%%)", trainable, total, 100 * trainable / total)

    def train(self, train_dataset_path: str | Path, eval_dataset_path: str | Path | None = None) -> dict[str, Any]:
        use_wandb = False
        run = None
        try:
            import wandb
            run = wandb.init(
                project=self.wandb_project,
                entity=self.wandb_entity,
                name=self.wandb_run_name,
                group="sft_training",
                job_type="train",
                config={
                    "model_name": self.model_name,
                    "learning_rate": self.learning_rate,
                    "num_epochs": self.num_epochs,
                    "batch_size": self.batch_size,
                    "use_lora": self.use_lora,
                    "lora_rank": self.lora_rank,
                    "trainer": "sft",
                },
            )
            use_wandb = True
        except Exception:
            logger.warning("wandb not available, logging to file only")

        try:
            train_dataset = SFTDataset(train_dataset_path, self.tokenizer, self.max_length)
            train_loader = DataLoader(train_dataset, batch_size=self.batch_size, shuffle=True)

            num_training_steps = len(train_loader) * self.num_epochs
            optimizer = AdamW(
                [p for p in self.model.parameters() if p.requires_grad],
                lr=self.learning_rate,
            )
            scheduler = get_linear_schedule_with_warmup(
                optimizer,
                num_warmup_steps=self.warmup_steps,
                num_training_steps=num_training_steps,
            )

            train_history: dict[str, Any] = {"epoch_losses": [], "batch_losses": []}
            global_step = 0

            self.model.train()
            for epoch in range(self.num_epochs):
                epoch_loss = 0.0

                for batch_idx, batch in enumerate(train_loader):
                    input_ids = batch["input_ids"].to(self.device)
                    attention_mask = batch["attention_mask"].to(self.device)
                    labels = batch["labels"].to(self.device)

                    outputs = self.model(
                        input_ids=input_ids,
                        attention_mask=attention_mask,
                        labels=labels,
                    )
                    loss = outputs.loss

                    optimizer.zero_grad()
                    loss.backward()
                    torch.nn.utils.clip_grad_norm_(self.model.parameters(), max_norm=1.0)
                    optimizer.step()
                    scheduler.step()

                    loss_val = loss.item()
                    perplexity = math.exp(min(loss_val, 20))  # clamp to avoid overflow
                    epoch_loss += loss_val
                    train_history["batch_losses"].append(loss_val)
                    global_step += 1

                    if use_wandb:
                        wandb.log({
                            "train/loss": loss_val,
                            "train/perplexity": perplexity,
                            "train/learning_rate": scheduler.get_last_lr()[0],
                        }, step=global_step)

                    if (batch_idx + 1) % 10 == 0:
                        logger.info(
                            "epoch %d/%d batch %d/%d loss=%.4f ppl=%.2f",
                            epoch + 1, self.num_epochs, batch_idx + 1, len(train_loader),
                            loss_val, perplexity,
                        )

                avg_epoch_loss = epoch_loss / len(train_loader)
                avg_epoch_ppl = math.exp(min(avg_epoch_loss, 20))
                train_history["epoch_losses"].append(avg_epoch_loss)

                if use_wandb:
                    wandb.log({
                        "train/epoch_loss": avg_epoch_loss,
                        "train/epoch_perplexity": avg_epoch_ppl,
                        "epoch": epoch + 1,
                    }, step=global_step)

                logger.info("epoch %d/%d avg_loss=%.4f ppl=%.2f", epoch + 1, self.num_epochs, avg_epoch_loss, avg_epoch_ppl)

                self.save_checkpoint(self.output_dir / f"epoch_{epoch + 1}")

            if eval_dataset_path and Path(eval_dataset_path).exists():
                eval_results = self._evaluate(eval_dataset_path)
                train_history["eval_results"] = eval_results
                if use_wandb:
                    wandb.log({
                        "eval/loss": eval_results["eval_loss"],
                        "eval/perplexity": eval_results["eval_perplexity"],
                    }, step=global_step)
                logger.info("eval loss=%.4f ppl=%.2f", eval_results["eval_loss"], eval_results["eval_perplexity"])

            if use_wandb:
                wandb.summary.update({
                    "final_train_loss": train_history["epoch_losses"][-1] if train_history["epoch_losses"] else None,
                    "model_name": self.model_name,
                })

        finally:
            if run is not None:
                run.finish()

        return train_history

    def _evaluate(self, eval_dataset_path: str | Path) -> dict[str, Any]:
        dataset = SFTDataset(eval_dataset_path, self.tokenizer, self.max_length)
        loader = DataLoader(dataset, batch_size=self.batch_size, shuffle=False)

        self.model.eval()
        total_loss = 0.0

        with torch.no_grad():
            for batch in loader:
                outputs = self.model(
                    input_ids=batch["input_ids"].to(self.device),
                    attention_mask=batch["attention_mask"].to(self.device),
                    labels=batch["labels"].to(self.device),
                )
                total_loss += outputs.loss.item()

        avg_loss = total_loss / len(loader) if loader else 0.0
        return {
            "eval_loss": avg_loss,
            "eval_perplexity": math.exp(min(avg_loss, 20)),
        }

    def save_checkpoint(self, checkpoint_dir: str | Path | None = None) -> str:
        if checkpoint_dir is None:
            checkpoint_dir = self.output_dir / "final_model"

        checkpoint_dir = Path(checkpoint_dir)
        checkpoint_dir.mkdir(parents=True, exist_ok=True)

        self.model.save_pretrained(str(checkpoint_dir))
        self.tokenizer.save_pretrained(str(checkpoint_dir))

        logger.info("saved: %s", checkpoint_dir)
        return str(checkpoint_dir)



def build_sft_dataset(
    spec_ids: list[int],
    output_path: Path | None = None,
    prompt_prefix: str = "Generate a TLA+ specification for the following system:\n\n",
) -> Path:
    if output_path is None:
        output_path = outputs_dir() / "sft_dataset.jsonl"

    output_path.parent.mkdir(parents=True, exist_ok=True)
    written = 0

    with open(output_path, "w") as out:
        for spec_id in spec_ids:
            desc_path = data_dir() / "descriptions" / f"{spec_id}.txt"
            tla_path = data_dir() / "tla_files" / f"{spec_id}.tla"

            if not desc_path.exists() or not tla_path.exists():
                logger.warning("spec=%d: missing description or tla file, skipping", spec_id)
                continue

            description = load_text(desc_path).strip()
            tla_spec = load_text(tla_path).strip()

            record = {
                "spec_id": spec_id,
                "prompt": prompt_prefix + description + "\n\nTLA+ Specification:\n",
                "completion": tla_spec,
            }
            out.write(json.dumps(record) + "\n")
            written += 1

    logger.info("SFT dataset written: %s (%d records)", output_path, written)
    return output_path


# entry point

def train_sft_model(
    base_model: str,
    train_dataset_path: str | Path,
    eval_dataset_path: str | Path | None = None,
    output_dir: str | Path | None = None,
    config: dict[str, Any] | None = None,
    wandb_project: str = "tla_bench",
    wandb_entity: str | None = None,
) -> dict[str, Any]:
    if output_dir is None:
        output_dir = outputs_dir() / "sft_models"

    if config is None:
        config = {
            "learning_rate": 2e-4,
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

    trainer = SFTTrainer(
        model_name=base_model,
        output_dir=output_dir,
        learning_rate=config.get("learning_rate", 2e-4),
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

    logger.info("Starting SFT training with config: %s", config)
    train_history = trainer.train(train_dataset_path, eval_dataset_path)

    results = {
        "base_model": base_model,
        "config": config,
        "train_history": train_history,
        "checkpoint_path": trainer.save_checkpoint(),
    }

    save_json(results, output_dir / "sft_training_results.json")
    logger.info("SFT training complete, results saved to %s", output_dir)
    return results


def main():
    import argparse

    parser = argparse.ArgumentParser(description="SFT fine-tuning on raw TLA+ corpus")
    parser.add_argument("--base-model", required=True)
    parser.add_argument("--train-dataset", required=True, help="JSONL with prompt/completion pairs")
    parser.add_argument("--eval-dataset", default=None)
    parser.add_argument("--output-dir", default=None)
    parser.add_argument("--build-dataset", action="store_true", help="Build SFT JSONL from raw corpus first")
    parser.add_argument("--spec-ids", default=None, help="Comma-separated spec IDs for dataset building")
    parser.add_argument("--learning-rate", type=float, default=2e-4)
    parser.add_argument("--num-epochs", type=int, default=5)
    parser.add_argument("--batch-size", type=int, default=4)
    parser.add_argument("--warmup-steps", type=int, default=100)
    parser.add_argument("--max-length", type=int, default=2048)
    parser.add_argument("--lora-rank", type=int, default=16)
    parser.add_argument("--lora-alpha", type=int, default=32)
    parser.add_argument("--lora-dropout", type=float, default=0.05)
    parser.add_argument("--no-lora", action="store_true")
    parser.add_argument("--wandb-project", default="tla_bench")
    parser.add_argument("--wandb-entity", default=None)
    args = parser.parse_args()

    if args.build_dataset:
        from utils import load_json, data_dir
        if args.spec_ids:
            spec_ids = [int(x) for x in args.spec_ids.split(",")]
        else:
            split = load_json(data_dir() / "test_split.json")
            spec_ids = split.get("train_ids", split.get("test_ids", []))
        build_sft_dataset(spec_ids, Path(args.train_dataset))

    config = {
        "learning_rate": args.learning_rate,
        "num_epochs": args.num_epochs,
        "batch_size": args.batch_size,
        "warmup_steps": args.warmup_steps,
        "max_length": args.max_length,
        "use_lora": not args.no_lora,
        "lora_rank": args.lora_rank,
        "lora_alpha": args.lora_alpha,
        "lora_dropout": args.lora_dropout,
    }

    train_sft_model(
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
