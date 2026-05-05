from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger, load_json, outputs_dir, repo_root, save_json

logger = get_logger("orchestrator")


class PipelineOrchestrator:
    def __init__(self, config_path: Path | None = None):
        if config_path is None:
            config_path = repo_root() / "configs/pipeline_config.json"
        
        self.config_path = config_path
        if self.config_path.exists():
            self.config = load_json(self.config_path)
        else:
            self.config = self._default_config()
    
    def _default_config(self) -> dict[str, Any]:
        return {
            "pipeline_stages": [
                "preference_generation",
                "model_training",
                "model_evaluation",
                "metrics_computation",
            ],
            "preference_generation": {
                "num_candidates": 5,
                "conditions": ["nlp_to_tla", "v2_to_tla", "v3_to_tla"],
            },
            "model_training": {
                "base_model": "meta-llama/Llama-2-7b-hf",
                "beta": 0.1,
                "learning_rate": 5e-7,
                "num_epochs": 3,
                "batch_size": 4,
                "warmup_steps": 100,
            },
            "model_evaluation": {
                "compute_code_quality": True,
                "compute_codebleu": True,
            },
            "metrics_computation": {
                "output_formats": ["csv", "json"],
            },
        }
    
    def save_config(self) -> None:
        self.config_path.parent.mkdir(parents=True, exist_ok=True)
        save_json(self.config, self.config_path)
        logger.info("Pipeline config saved: %s", self.config_path)
    
    def generate_preferences(self, limit: int | None = None) -> str:
        from preference_generator import generate_preference_dataset
        
        logger.info("Stage: Preference Generation")
        
        split = load_json(repo_root() / "data" / "test_split.json")
        test_ids = split["test_ids"]
        if limit:
            test_ids = test_ids[:limit]
        
        models_cfg = load_json(repo_root() / "configs/models.json")
        conditions = self.config["preference_generation"]["conditions"]
        num_candidates = self.config["preference_generation"]["num_candidates"]
        
        output_path = outputs_dir() / "preference_dataset.jsonl"
        generate_preference_dataset(
            test_ids=test_ids,
            model_configs=models_cfg,
            conditions=conditions,
            num_candidates=num_candidates,
            output_path=output_path,
        )
        
        logger.info("Preference dataset generated: %s", output_path)
        return str(output_path)
    
    def train_model(self, dataset_path: str | Path) -> str:
        from dpo_trainer import train_dpo_model
        
        logger.info("Stage: Model Training (DPO)")
        
        config = self.config["model_training"]
        output_dir = outputs_dir() / "dpo_models"
        
        results = train_dpo_model(
            base_model=config["base_model"],
            train_dataset_path=dataset_path,
            output_dir=output_dir,
            config={
                "beta": config["beta"],
                "learning_rate": config["learning_rate"],
                "num_epochs": config["num_epochs"],
                "batch_size": config["batch_size"],
                "warmup_steps": config["warmup_steps"],
            },
        )
        
        checkpoint_path = results["checkpoint_path"]
        logger.info("Model training complete: %s", checkpoint_path)
        return checkpoint_path
    
    def evaluate_model(self, model_path: str | Path | None = None) -> dict[str, Any]:
        from evaluation import SpecificationEvaluator
        
        logger.info("Stage: Model Evaluation")
        
        evaluator = SpecificationEvaluator()
        analysis = evaluator.compute_cross_model_analysis()
        
        logger.info("Model evaluation complete")
        return analysis
    
    def compute_metrics(self) -> dict[str, Any]:
        from metrics import (
            compute_summary,
            write_summary_csv,
            compute_comparison,
            write_comparison_csv,
            write_detailed_metrics_csv,
        )
        
        logger.info("Stage: Metrics Computation")
        
        summary = compute_summary()
        write_summary_csv(summary)
        
        comparison = compute_comparison()
        write_comparison_csv(comparison)
        
        models_cfg = load_json(repo_root() / "configs/models.json")
        for model_cfg in models_cfg:
            write_detailed_metrics_csv(model_cfg["id"])
        
        logger.info("Metrics computation complete")
        return {
            "summary_rows": len(summary),
            "comparison_rows": len(comparison),
            "models_processed": len(models_cfg),
        }
    
    def run_full_pipeline(self, limit: int | None = None, skip_training: bool = False) -> dict[str, Any]:
        logger.info("Starting full pipeline")
        
        results = {
            "timestamp": __import__("datetime").datetime.now().isoformat(),
            "stages": {},
        }
        
        try:
            dataset_path = self.generate_preferences(limit=limit)
            results["stages"]["preference_generation"] = {
                "status": "success",
                "dataset_path": dataset_path,
            }
        except Exception as exc:
            logger.error("Preference generation failed: %s", exc)
            results["stages"]["preference_generation"] = {
                "status": "failed",
                "error": str(exc),
            }
            return results
        
        if not skip_training:
            try:
                model_path = self.train_model(dataset_path)
                results["stages"]["model_training"] = {
                    "status": "success",
                    "model_path": model_path,
                }
            except Exception as exc:
                logger.error("Model training failed: %s", exc)
                results["stages"]["model_training"] = {
                    "status": "failed",
                    "error": str(exc),
                }
                return results
        
        try:
            evaluation = self.evaluate_model()
            results["stages"]["model_evaluation"] = {
                "status": "success",
                "analysis": evaluation,
            }
        except Exception as exc:
            logger.error("Model evaluation failed: %s", exc)
            results["stages"]["model_evaluation"] = {
                "status": "failed",
                "error": str(exc),
            }
        
        try:
            metrics = self.compute_metrics()
            results["stages"]["metrics_computation"] = {
                "status": "success",
                "metrics": metrics,
            }
        except Exception as exc:
            logger.error("Metrics computation failed: %s", exc)
            results["stages"]["metrics_computation"] = {
                "status": "failed",
                "error": str(exc),
            }
        
        pipeline_report = outputs_dir() / "pipeline_report.json"
        save_json(results, pipeline_report)
        logger.info("Pipeline complete, report: %s", pipeline_report)
        
        return results


def main():
    import argparse
    
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", choices=["preferences", "train", "evaluate", "metrics", "full"], default="full")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--skip-training", action="store_true")
    parser.add_argument("--dataset-path", help="Path to preference dataset for training")
    args = parser.parse_args()
    
    orchestrator = PipelineOrchestrator()
    
    if args.stage == "full":
        orchestrator.run_full_pipeline(limit=args.limit, skip_training=args.skip_training)
    elif args.stage == "preferences":
        orchestrator.generate_preferences(limit=args.limit)
    elif args.stage == "train":
        if not args.dataset_path:
            logger.error("--dataset-path required for train stage")
            return
        orchestrator.train_model(args.dataset_path)
    elif args.stage == "evaluate":
        orchestrator.evaluate_model()
    elif args.stage == "metrics":
        orchestrator.compute_metrics()


if __name__ == "__main__":
    main()
