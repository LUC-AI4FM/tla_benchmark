#!/usr/bin/env python3
"""
Train Spec-Align using DPO with Mistral-7B-Instruct
Uses preference dataset to fine-tune model with Direct Preference Optimization
"""

import json
import torch
import logging
from pathlib import Path
from transformers import AutoTokenizer, AutoModelForCausalLM, TrainingArguments
from peft import LoraConfig, get_peft_model
from trl import DPOTrainer
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

def train_dpo(
    model_name: str = "mistralai/Mistral-7B-Instruct-v0.2",
    dataset_path: str = "outputs/preference_dataset.jsonl",
    output_dir: str = "outputs/dpo_models/mistral_dpo",
    num_train_epochs: int = 1,
    batch_size: int = 1,
    lr: float = 5e-7
):
    """Fine-tune model with DPO"""
    
    logger.info(f"Loading base model: {model_name}")
    
    # Load tokenizer and model
    tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)
    tokenizer.pad_token = tokenizer.eos_token
    
    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        torch_dtype=torch.float16,
        device_map="auto"
    )
    logger.info(f"✓ Model loaded (dtype={model.dtype}, device={next(model.parameters()).device})")
    
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
    
    # Create training arguments
    training_args = TrainingArguments(
        output_dir=output_dir,
        num_train_epochs=num_train_epochs,
        per_device_train_batch_size=batch_size,
        learning_rate=lr,
        bf16=True,
        logging_steps=5,
        save_steps=50,
        eval_strategy="no",
        remove_unused_columns=False
    )
    
    # Create DPO trainer
    trainer = DPOTrainer(
        model=model,
        args=training_args,
        train_dataset=preference_data,
        tokenizer=tokenizer,
        beta=0.1,
        max_prompt_length=256,
        max_completion_length=512,
    )
    
    logger.info("Starting DPO training...")
    trainer.train()
    
    # Save model
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
        "lora_rank": 16,
        "status": "completed"
    }
    with open(f"{output_dir}/training_metadata.json", "w") as f:
        json.dump(metadata, f, indent=2)
    
    logger.info(f"✓ Training complete! Model saved to {output_dir}")
    logger.info(f"✓ Metadata: {json.dumps(metadata, indent=2)}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Train Spec-Align with DPO")
    parser.add_argument("--model", default="mistralai/Mistral-7B-Instruct-v0.2", help="Model name")
    parser.add_argument("--dataset", default="outputs/preference_dataset.jsonl", help="Dataset path")
    parser.add_argument("--output", default="outputs/dpo_models/mistral_dpo", help="Output directory")
    parser.add_argument("--epochs", type=int, default=1, help="Number of epochs")
    parser.add_argument("--batch-size", type=int, default=1, help="Batch size")
    parser.add_argument("--lr", type=float, default=5e-7, help="Learning rate")
    
    args = parser.parse_args()
    
    train_dpo(
        model_name=args.model,
        dataset_path=args.dataset,
        output_dir=args.output,
        num_train_epochs=args.epochs,
        batch_size=args.batch_size,
        lr=args.lr
    )
