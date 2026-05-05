from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger, load_json, outputs_dir, repo_root, results_dir, save_json
from code_quality_metrics import (
    compute_code_quality_metrics,
    compare_code_quality,
    extract_ast,
    codebleu_ast_similarity,
)

logger = get_logger("evaluation")


class SpecificationEvaluator:
    def __init__(self, output_dir: Path | None = None):
        self.output_dir = output_dir or outputs_dir() / "evaluation"
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def evaluate_model_on_condition(
        self,
        model_id: str,
        condition: str,
    ) -> dict[str, Any]:
        validation_dir = outputs_dir() / "validation" / model_id / condition
        
        if not validation_dir.exists():
            logger.warning("Validation dir not found: %s", validation_dir)
            return {}
        
        summaries = []
        for f in sorted(validation_dir.glob("*_summary.json")):
            try:
                summaries.append(load_json(f))
            except Exception:
                pass
        
        if not summaries:
            return {}
        
        total = len(summaries)
        sany_pass = sum(1 for s in summaries if s.get("sany_pass", False))
        tlc_pass = sum(1 for s in summaries if s.get("tlc_pass", False))
        
        error_classifications = []
        for f in sorted(validation_dir.glob("*_errors.json")):
            try:
                error_classifications.append(load_json(f))
            except Exception:
                pass
        
        error_patterns = {}
        if error_classifications:
            for error_cat in error_classifications[0].keys():
                error_patterns[error_cat] = sum(
                    1 for e in error_classifications if e.get(error_cat, False)
                ) / len(error_classifications)
        
        results = {
            "model_id": model_id,
            "condition": condition,
            "total_specs": total,
            "sany_pass": sany_pass,
            "sany_rate": round(sany_pass / total, 4) if total > 0 else 0.0,
            "tlc_pass": tlc_pass,
            "tlc_rate": round(tlc_pass / total, 4) if total > 0 else 0.0,
            "error_patterns": error_patterns,
        }
        
        return results
    
    def evaluate_all_models_on_condition(
        self,
        condition: str,
    ) -> list[dict[str, Any]]:
        models_cfg = load_json(repo_root() / "configs/models.json")
        results = []
        
        for model_cfg in models_cfg:
            result = self.evaluate_model_on_condition(model_cfg["id"], condition)
            if result:
                results.append(result)
        
        return results
    
    def compute_cross_model_analysis(self) -> dict[str, Any]:
        models_cfg = load_json(repo_root() / "configs/models.json")
        conditions = ["nlp_to_tla", "v2_to_tla", "v3_to_tla"]
        
        all_results = []
        for condition in conditions:
            all_results.extend(self.evaluate_all_models_on_condition(condition))
        
        if not all_results:
            return {}
        
        shared_blindspots = self._identify_shared_blindspots(all_results)
        
        analysis = {
            "total_models": len(models_cfg),
            "conditions": conditions,
            "per_model_results": all_results,
            "shared_blindspots": shared_blindspots,
        }
        
        return analysis
    
    def _identify_shared_blindspots(self, results: list[dict[str, Any]]) -> dict[str, Any]:
        error_pattern_by_condition = {}
        
        for result in results:
            condition = result["condition"]
            if condition not in error_pattern_by_condition:
                error_pattern_by_condition[condition] = {}
            
            for error_type, rate in result.get("error_patterns", {}).items():
                if error_type not in error_pattern_by_condition[condition]:
                    error_pattern_by_condition[condition][error_type] = []
                error_pattern_by_condition[condition][error_type].append(rate)
        
        blindspots = {}
        for condition, patterns in error_pattern_by_condition.items():
            blindspots[condition] = {}
            for error_type, rates in patterns.items():
                avg_rate = sum(rates) / len(rates) if rates else 0.0
                if avg_rate > 0.5:
                    blindspots[condition][error_type] = round(avg_rate, 4)
        
        return blindspots
    
    def compute_progress_metrics(
        self,
        baseline_results: list[dict[str, Any]],
        finetuned_results: list[dict[str, Any]],
    ) -> dict[str, Any]:
        baseline_by_condition = {r["condition"]: r for r in baseline_results}
        finetuned_by_condition = {r["condition"]: r for r in finetuned_results}
        
        progress = {}
        for condition in baseline_by_condition.keys():
            baseline = baseline_by_condition[condition]
            finetuned = finetuned_by_condition.get(condition, {})
            
            baseline_tlc_rate = baseline.get("tlc_rate", 0.0)
            finetuned_tlc_rate = finetuned.get("tlc_rate", 0.0)
            
            improvement = finetuned_tlc_rate - baseline_tlc_rate
            relative_improvement = (improvement / baseline_tlc_rate * 100) if baseline_tlc_rate > 0 else 0.0
            
            progress[condition] = {
                "baseline_tlc_rate": baseline_tlc_rate,
                "finetuned_tlc_rate": finetuned_tlc_rate,
                "absolute_improvement": round(improvement, 4),
                "relative_improvement_percent": round(relative_improvement, 2),
            }
        
        return progress
    
    def save_evaluation_report(self, data: dict[str, Any], filename: str = "evaluation_report.json") -> None:
        report_path = self.output_dir / filename
        save_json(data, report_path)
        logger.info("Evaluation report saved: %s", report_path)


def run_comprehensive_evaluation() -> dict[str, Any]:
    evaluator = SpecificationEvaluator()
    
    analysis = evaluator.compute_cross_model_analysis()
    evaluator.save_evaluation_report(analysis, "cross_model_analysis.json")
    
    conditions = ["nlp_to_tla", "v2_to_tla", "v3_to_tla"]
    for condition in conditions:
        results = evaluator.evaluate_all_models_on_condition(condition)
        condition_report = {
            "condition": condition,
            "models": results,
        }
        evaluator.save_evaluation_report(condition_report, f"evaluation_{condition}.json")
    
    logger.info("Comprehensive evaluation complete")
    return analysis


def main():
    import argparse
    
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", help="Specific model to evaluate")
    parser.add_argument("--condition", help="Specific condition to evaluate")
    parser.add_argument("--comparison", action="store_true", help="Run cross-model comparison")
    args = parser.parse_args()
    
    evaluator = SpecificationEvaluator()
    
    if args.comparison:
        run_comprehensive_evaluation()
    elif args.model and args.condition:
        result = evaluator.evaluate_model_on_condition(args.model, args.condition)
        evaluator.save_evaluation_report(result, f"eval_{args.model}_{args.condition}.json")
        print(json.dumps(result, indent=2))
    else:
        run_comprehensive_evaluation()


if __name__ == "__main__":
    main()
