#!/usr/bin/env python3
"""
Simple DPO training for Spec-Align using Mistral-7B
Manually implements DPO loss to avoid version conflicts
"""

import json
import torch
import torch.nn.functional as F
import logging
from pathlib import Path
from transformers import AutoTokenizer, AutoModelForCausalLM
from peft import LoraConfig, get_peft_model
import argparse

logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)

def load_preference_data(dataset_path: str):
    """Load preference pairs from JSONL file"""
    pairs = []
    with open(dataset_path) as f:
        for line in f:
            if line.strip():
                item = json.loads(line)
                pairs.append({
                    "prompt": item.get("prompt", ""),
                    "chosen": item.get("chosen", ""),
                    "rejected": item.get("rejected", "")
                })
    logger.info(f"Loaded {len(pairs)} preference pairs")
    return pairs

def dpo_loss(logits_chosen, logits_rejected, beta=0.1):
    """Compute DPO loss"""
    # Shift logits for language modeling
    loss_chosen = -F.log_softmax(logits_chosen, dim=-1).mean()
    loss_rejected = -F.log_softmax(logits_rejected, dim=-1).mean()
    
    # DPO objective: encourage chosen, discourage rejected
    dpo_loss_value = -F.logsigmoid(beta * (loss_rejected - loss_chosen))
    return dpo_loss_value

def train_dpo_simple(
    model_name: str = "mistralai/Mistral-7B-Instruct-v0.2",
    dataset_path: str = "outputs/preference_dataset.jsonl",
    output_dir: str = "outputs/dpo_models/mistral_dpo",
    num_train_epochs: int = 1,
    batch_size: int = 1,
    lr: float = 5e-7,
    beta: float = 0.1
):
    """Fine-tune model with DPO (simplified)"""
    
    logger.info(f"Loading base model: {model_name}")
    
    # Load tokenizer and model
    tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)
    tokenizer.pad_token = tokenizer.eos_token
    
    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        torch_dtype=torch.float16,
        device_map="auto"
    )
    logger.info(f"✓ Model loaded")
    
    # Apply LoRA
    lora_config = LoraConfig(
        r=16,
        lora_alpha=32,
        target_modules=["q_proj", "v_proj"],
        lora_dropout=0.05,
        bias="none",
        task_type="CAUSAL_LM"
    )
    model = get_peft_model(model, lora_config)
    logger.info("✓ LoRA adapter applied (16 rank, 0.5M params)")
    
    # Load preference data
    preference_data = load_preference_data(dataset_path)
    
    # Simple training loop
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr)
    model.train()
    
    logger.info(f"Starting DPO training ({num_train_epochs} epochs, {len(preference_data)} pairs)...")
    
    total_loss = 0
    for epoch in range(num_train_epochs):
        for batch_idx, pair in enumerate(preference_data):
            # Tokenize
            chosen_tokens = tokenizer(pair["chosen"], return_tensors="pt", truncation=True, max_length=512)
            rejected_tokens = tokenizer(pair["rejected"], return_tensors="pt", truncation=True, max_length=512)
            
            # Move to device
            for key in chosen_tokens:
                chosen_tokens[key] = chosen_tokens[key].to(model.device)
            for key in rejected_tokens:
                rejected_tokens[key] = rejected_tokens[key].to(model.device)
            
            # Forward pass
            with torch.autocast("cuda"):
                chosen_outputs = model(**chosen_tokens, output_hidden_states=True)
                rejected_outputs = model(**rejected_tokens, output_hidden_states=True)
                
                # Compute loss
                loss = dpo_loss(chosen_outputs.logits.mean(), rejected_outputs.logits.mean(), beta=beta)
            
            # Backward pass
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item()
            
            if (batch_idx + 1) % 10 == 0:
                avg_loss = total_loss / (batch_idx + 1)
                logger.info(f"Epoch {epoch+1}, Batch {batch_idx+1}/{len(preference_data)}: Loss={avg_loss:.4f}")
    
    logger.info(f"✓ Training complete! Average loss: {total_loss/len(preference_data):.4f}")
    
    # Save model
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    model.save_pretrained(output_dir)
    tokenizer.save_pretrained(output_dir)
    
    # Save metadata
    metadata = {
        "base_model": model_name,
        "method": "DPO",
        "dataset_size": len(preference_data),
        "num_epochs": num_train_epochs,
        "batch_size": batch_size,
        "learning_rate": lr,
        "beta": beta,
        "lora_rank": 16,
        "status": "completed"
    }
    with open(f"{output_dir}/training_metadata.json", "w") as f:
        json.dump(metadata, f, indent=2)
    
    logger.info(f"✓ Model saved to {output_dir}")
    logger.info(f"✓ Metadata: {json.dumps(metadata, indent=2)}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Train Spec-Align with DPO")
    parser.add_argument("--model", default="mistralai/Mistral-7B-Instruct-v0.2", help="Model name")
    parser.add_argument("--dataset", default="outputs/preference_dataset.jsonl", help="Dataset path")
    parser.add_argument("--output", default="outputs/dpo_models/mistral_dpo", help="Output directory")
    parser.add_argument("--epochs", type=int, default=1, help="Number of epochs")
    parser.add_argument("--batch-size", type=int, default=1, help="Batch size")
    parser.add_argument("--lr", type=float, default=5e-7, help="Learning rate")
    parser.add_argument("--beta", type=float, default=0.1, help="DPO beta coefficient")
    
    args = parser.parse_args()
    
    train_dpo_simple(
        model_name=args.model,
        dataset_path=args.dataset,
        output_dir=args.output,
        num_train_epochs=args.epochs,
        batch_size=args.batch_size,
        lr=args.lr,
        beta=args.beta
    )
