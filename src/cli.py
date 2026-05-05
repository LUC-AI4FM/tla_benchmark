#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

import argparse
from utils import get_logger

logger = get_logger("cli")


def main():
    parser = argparse.ArgumentParser(
        description="TLA-Bench: Benchmark for Formal Verification Reasoning",
        prog="tla-bench",
    )
    subparsers = parser.add_subparsers(dest="command", help="Available commands")
    
    preferences_parser = subparsers.add_parser("preferences", help="Generate preference dataset")
    preferences_parser.add_argument("--limit", type=int, help="Limit number of specs")
    preferences_parser.add_argument("--candidates", type=int, default=5, help="Candidates per spec")
    preferences_parser.add_argument("--output", help="Output file path")
    
    train_parser = subparsers.add_parser("train", help="Train DPO model")
    train_parser.add_argument("--base-model", required=True, help="Base model name or path")
    train_parser.add_argument("--train-dataset", required=True, help="Training dataset path")
    train_parser.add_argument("--eval-dataset", help="Evaluation dataset path")
    train_parser.add_argument("--output-dir", help="Output directory")
    train_parser.add_argument("--beta", type=float, default=0.1)
    train_parser.add_argument("--learning-rate", type=float, default=5e-7)
    train_parser.add_argument("--num-epochs", type=int, default=3)
    train_parser.add_argument("--batch-size", type=int, default=4)
    
    eval_parser = subparsers.add_parser("evaluate", help="Evaluate models")
    eval_parser.add_argument("--model", help="Specific model to evaluate")
    eval_parser.add_argument("--condition", help="Specific condition")
    eval_parser.add_argument("--comparison", action="store_true", help="Cross-model analysis")
    
    metrics_parser = subparsers.add_parser("metrics", help="Compute evaluation metrics")
    
    run_parser = subparsers.add_parser("run", help="Run full pipeline")
    run_parser.add_argument("--limit", type=int, help="Limit number of specs")
    run_parser.add_argument("--skip-training", action="store_true")
    
    runner_parser = subparsers.add_parser("generate", help="Run spec generation")
    runner_parser.add_argument("--model", help="Specific model")
    runner_parser.add_argument("--condition", choices=["nlp_to_tla", "v2_to_tla", "v3_to_tla", "all"], default="all")
    runner_parser.add_argument("--limit", type=int)
    runner_parser.add_argument("--api-key", default="")
    runner_parser.add_argument("--gpu-id", type=int, default=0)
    
    args = parser.parse_args()
    
    if args.command == "preferences":
        from preference_generator import generate_preference_dataset
        from utils import data_dir, load_json, repo_root, outputs_dir
        
        split = load_json(data_dir() / "test_split.json")
        test_ids = split["test_ids"]
        if args.limit:
            test_ids = test_ids[:args.limit]
        
        models_cfg = load_json(repo_root() / "configs/models.json")
        output_path = Path(args.output) if args.output else outputs_dir() / "preference_dataset.jsonl"
        
        generate_preference_dataset(
            test_ids,
            models_cfg,
            ["nlp_to_tla", "v2_to_tla", "v3_to_tla"],
            num_candidates=args.candidates,
            output_path=output_path,
        )
        logger.info("Preference dataset generated: %s", output_path)
    
    elif args.command == "train":
        from dpo_trainer import train_dpo_model
        
        config = {
            "beta": args.beta,
            "learning_rate": args.learning_rate,
            "num_epochs": args.num_epochs,
            "batch_size": args.batch_size,
        }
        
        train_dpo_model(
            base_model=args.base_model,
            train_dataset_path=args.train_dataset,
            eval_dataset_path=args.eval_dataset,
            output_dir=args.output_dir,
            config=config,
        )
    
    elif args.command == "evaluate":
        from evaluation import SpecificationEvaluator, run_comprehensive_evaluation
        
        if args.comparison:
            run_comprehensive_evaluation()
        else:
            evaluator = SpecificationEvaluator()
            if args.model and args.condition:
                result = evaluator.evaluate_model_on_condition(args.model, args.condition)
                import json
                print(json.dumps(result, indent=2))
            else:
                run_comprehensive_evaluation()
    
    elif args.command == "metrics":
        from metrics import compute_summary, write_summary_csv, compute_comparison, write_comparison_csv
        
        summary = compute_summary()
        write_summary_csv(summary)
        comparison = compute_comparison()
        write_comparison_csv(comparison)
        logger.info("Metrics computed")
    
    elif args.command == "run":
        from orchestrator import PipelineOrchestrator
        
        orch = PipelineOrchestrator()
        orch.run_full_pipeline(limit=args.limit, skip_training=args.skip_training)
    
    elif args.command == "generate":
        from runner import run_all
        from utils import data_dir, load_json, repo_root, outputs_dir
        
        models_cfg = load_json(repo_root() / "configs/models.json")
        split = load_json(data_dir() / "test_split.json")
        test_ids = split["test_ids"]
        if args.limit:
            test_ids = test_ids[:args.limit]
        
        if args.model:
            models_cfg = [m for m in models_cfg if m["id"] == args.model]
        
        conditions = ["nlp_to_tla", "v2_to_tla", "v3_to_tla"] if args.condition == "all" else [args.condition]
        
        for model_cfg in models_cfg:
            logger.info("Running model: %s", model_cfg["id"])
            results = run_all(model_cfg, test_ids, conditions, api_key=args.api_key, gpu_id=args.gpu_id)
            output_file = outputs_dir() / f"run_{model_cfg['id']}.json"
            from utils import save_json
            save_json(results, output_file)
            logger.info("Results saved: %s", output_file)
    
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
