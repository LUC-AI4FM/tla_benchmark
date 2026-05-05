from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Tuple
from dataclasses import dataclass, asdict

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger, load_json, load_text, data_dir, outputs_dir, save_json, get_ast_spec_by_id
from validator import validate_spec
from code_quality_metrics import (
    compute_codebleu,
    compute_cyclomatic_complexity,
    compute_halstead_metrics,
    compute_maintainability_index,
)
from parser import extract_tla_from_response

logger = get_logger("dpo_model_tester")


@dataclass
class ModelTestResult:
    spec_id: int
    model_name: str
    condition: str
    
    generated_tla: str | None
    generation_time_s: float
    
    sany_pass: bool
    tlc_pass: bool
    
    pass_rate_k1: bool
    
    codebleu_score: float | None
    cyclomatic_complexity: int | None
    halstead_effort: float | None
    maintainability_index: float | None
    
    preference_accuracy: float | None
    
    error: str | None = None


class DPOModelTester:
    def __init__(
        self,
        model_checkpoint: str,
        model_name: str = "spec-align",
        backend: str = "huggingface",
        wandb_project: str = "tla_bench",
        wandb_entity: str | None = None,
    ):
        self.model_checkpoint = model_checkpoint
        self.model_name = model_name
        self.backend = backend
        self.wandb_project = wandb_project
        self.wandb_entity = wandb_entity
        self.model = None
        self.tokenizer = None
        self._load_model()
    
    def _load_model(self):
        if self.backend == "huggingface":
            from transformers import AutoModelForCausalLM, AutoTokenizer
            
            logger.info(f"Loading model from {self.model_checkpoint}")
            self.tokenizer = AutoTokenizer.from_pretrained(self.model_checkpoint)
            self.model = AutoModelForCausalLM.from_pretrained(
                self.model_checkpoint,
                torch_dtype="auto",
                device_map="auto",
            )
            logger.info("Model loaded successfully")
    
    def generate_specification(
        self,
        prompt: str,
        max_tokens: int = 2048,
        temperature: float = 0.7,
    ) -> Tuple[str | None, float]:
        
        t0 = time.time()
        
        try:
            inputs = self.tokenizer(prompt, return_tensors="pt").to(self.model.device)
            
            outputs = self.model.generate(
                **inputs,
                max_new_tokens=max_tokens,
                temperature=temperature,
                top_p=0.95,
                do_sample=True,
                pad_token_id=self.tokenizer.eos_token_id,
            )
            
            generated_text = self.tokenizer.decode(outputs[0], skip_special_tokens=True)
            
            elapsed = time.time() - t0
            
            tla_spec = extract_tla_from_response(generated_text)
            
            logger.debug(
                f"Generated spec for prompt (len={len(prompt)}): tla_found={tla_spec is not None}, time={elapsed:.2f}s"
            )
            
            return tla_spec, elapsed
        
        except Exception as e:
            elapsed = time.time() - t0
            logger.error(f"Generation error: {e}")
            return None, elapsed
    
    def test_on_spec(
        self,
        spec_id: int,
        condition: str = "nlp_to_tla",
        num_attempts: int = 1,
        temperature: float = 0.7,
    ) -> List[ModelTestResult]:
        
        description_path = data_dir() / "descriptions" / f"{spec_id}.json"
        reference_tla_path = data_dir() / "tla_files" / f"{spec_id}.tla"
        cfg_path = data_dir() / "cfg" / f"{spec_id}.cfg"
        # Removed v3_path - now using consolidated AST
        
        if not description_path.exists():
            logger.warning(f"Spec {spec_id}: no description found")
            return []
        
        description_data = load_json(description_path)
        
        if isinstance(description_data, dict):
            prompt = description_data.get("system_overview", "") or json.dumps(description_data)
        else:
            prompt = str(description_data)
        
        reference_tla = None
        if reference_tla_path.exists():
            reference_tla = load_text(reference_tla_path)
        
        reference_ast = get_ast_spec_by_id(spec_id)
        
        results = []
        
        for attempt in range(num_attempts):
            
            generated_tla, gen_time = self.generate_specification(
                prompt,
                temperature=temperature,
            )
            
            sany_pass = False
            tlc_pass = False
            
            if generated_tla:
                temp_file = outputs_dir() / "temp" / f"{spec_id}_attempt_{attempt}.tla"
                temp_file.parent.mkdir(parents=True, exist_ok=True)
                
                temp_file.write_text(generated_tla)
                
                try:
                    validation_result = validate_spec(
                        str(temp_file),
                        str(cfg_path) if cfg_path.exists() else None,
                        str(temp_file.parent),
                        spec_id,
                        self.model_name,
                        condition,
                    )
                    
                    sany_pass = validation_result.get("sany_pass", False)
                    tlc_pass = validation_result.get("tlc_pass", False)
                
                except Exception as e:
                    logger.error(f"Validation error for spec {spec_id}: {e}")
                
                finally:
                    temp_file.unlink(missing_ok=True)
            
            codebleu = None
            cyclomatic = None
            halstead = None
            maintainability = None
            
            if generated_tla and reference_ast:
                try:
                    codebleu = compute_codebleu(generated_tla, reference_ast, spec_id)
                except Exception as e:
                    logger.debug(f"CodeBLEU computation failed: {e}")
            
            if generated_tla:
                try:
                    cyclomatic = compute_cyclomatic_complexity(generated_tla)
                except Exception as e:
                    logger.debug(f"Cyclomatic complexity computation failed: {e}")
                
                try:
                    halstead = compute_halstead_metrics(generated_tla)
                except Exception as e:
                    logger.debug(f"Halstead computation failed: {e}")
                
                try:
                    maintainability = compute_maintainability_index(generated_tla)
                except Exception as e:
                    logger.debug(f"Maintainability index computation failed: {e}")
            
            result = ModelTestResult(
                spec_id=spec_id,
                model_name=self.model_name,
                condition=condition,
                generated_tla=generated_tla,
                generation_time_s=gen_time,
                sany_pass=sany_pass,
                tlc_pass=tlc_pass,
                pass_rate_k1=(sany_pass and tlc_pass),
                codebleu_score=codebleu,
                cyclomatic_complexity=cyclomatic,
                halstead_effort=halstead.get("effort", None) if halstead else None,
                maintainability_index=maintainability,
                preference_accuracy=None,
            )
            
            results.append(result)
            
            codebleu_str = f"{codebleu:.3f}" if codebleu is not None else "N/A"
            logger.info(
                "spec_id=%d attempt=%d/%d sany=%s tlc=%s time=%.2fs codebleu=%s",
                spec_id, attempt + 1, num_attempts, sany_pass, tlc_pass, gen_time, codebleu_str,
            )
        
        return results
    
    def test_on_test_set(
        self,
        test_ids: List[int] | None = None,
        num_attempts: int = 3,
        temperature: float = 0.7,
    ) -> Dict[str, Any]:
        import wandb

        if test_ids is None:
            test_split_path = data_dir() / "test_split.json"
            if test_split_path.exists():
                test_ids = load_json(test_split_path).get("test_ids", [])
            else:
                logger.error("No test_ids provided and test_split.json not found")
                return {}

        run = wandb.init(
            project=self.wandb_project,
            entity=self.wandb_entity,
            name=f"test_{self.model_name}",
            group="model_testing",
            job_type="test",
            config={
                "model_name": self.model_name,
                "model_checkpoint": self.model_checkpoint,
                "num_attempts": num_attempts,
                "temperature": temperature,
                "num_specs": len(test_ids),
                "condition": "nlp_to_tla",
            },
        )

        spec_table = wandb.Table(columns=[
            "spec_id", "attempt", "sany_pass", "tlc_pass", "pass_k1",
            "codebleu", "cyclomatic_complexity", "maintainability_index",
            "generation_time_s", "error",
        ])

        all_results = []
        global_step = 0

        try:
            for spec_id in test_ids:
                try:
                    results = self.test_on_spec(
                        spec_id,
                        condition="nlp_to_tla",
                        num_attempts=num_attempts,
                        temperature=temperature,
                    )
                    all_results.extend(results)

                    for r in results:
                        global_step += 1
                        wandb.log({
                            "spec/sany_pass": int(r.sany_pass),
                            "spec/tlc_pass": int(r.tlc_pass),
                            "spec/pass_k1": int(r.pass_rate_k1),
                            "spec/codebleu": r.codebleu_score if r.codebleu_score is not None else 0.0,
                            "spec/cyclomatic_complexity": r.cyclomatic_complexity if r.cyclomatic_complexity is not None else 0.0,
                            "spec/maintainability_index": r.maintainability_index if r.maintainability_index is not None else 0.0,
                            "spec/generation_time_s": r.generation_time_s,
                        }, step=global_step)

                        spec_table.add_data(
                            r.spec_id, 0, r.sany_pass, r.tlc_pass, r.pass_rate_k1,
                            r.codebleu_score, r.cyclomatic_complexity, r.maintainability_index,
                            r.generation_time_s, r.error or "",
                        )

                except Exception as e:
                    logger.error("Error testing spec %s: %s", spec_id, e)
                    all_results.append(
                        ModelTestResult(
                            spec_id=spec_id,
                            model_name=self.model_name,
                            condition="nlp_to_tla",
                            generated_tla=None,
                            generation_time_s=0,
                            sany_pass=False,
                            tlc_pass=False,
                            pass_rate_k1=False,
                            codebleu_score=None,
                            cyclomatic_complexity=None,
                            halstead_effort=None,
                            maintainability_index=None,
                            preference_accuracy=None,
                            error=str(e),
                        )
                    )

            aggregated = self._aggregate_results(all_results)

            # Log aggregate summary metrics
            summary_metrics = {
                "test/sany_rate": aggregated.get("sany_rate", 0),
                "test/tlc_rate": aggregated.get("tlc_rate", 0),
                "test/pass_k1_rate": aggregated.get("pass_k1_rate", 0),
            }
            if aggregated.get("metrics", {}).get("codebleu", {}).get("mean") is not None:
                summary_metrics["test/avg_codebleu"] = aggregated["metrics"]["codebleu"]["mean"]
            if aggregated.get("metrics", {}).get("cyclomatic_complexity", {}).get("mean") is not None:
                summary_metrics["test/avg_cyclomatic_complexity"] = aggregated["metrics"]["cyclomatic_complexity"]["mean"]
            if aggregated.get("metrics", {}).get("maintainability_index", {}).get("mean") is not None:
                summary_metrics["test/avg_maintainability_index"] = aggregated["metrics"]["maintainability_index"]["mean"]
            if aggregated.get("generation", {}).get("avg_time_s") is not None:
                summary_metrics["test/avg_generation_time_s"] = aggregated["generation"]["avg_time_s"]

            wandb.log(summary_metrics, step=global_step)
            wandb.log({"results/spec_table": spec_table}, step=global_step)
            wandb.summary.update(summary_metrics)

            logger.info(
                "model=%s sany_rate=%.3f tlc_rate=%.3f pass_k1_rate=%.3f",
                self.model_name,
                aggregated.get("sany_rate", 0),
                aggregated.get("tlc_rate", 0),
                aggregated.get("pass_k1_rate", 0),
            )

        finally:
            run.finish()

        return aggregated
    
    def _aggregate_results(self, results: List[ModelTestResult]) -> Dict[str, Any]:
        
        if not results:
            return {}
        
        total = len(results)
        sany_pass_count = sum(1 for r in results if r.sany_pass)
        tlc_pass_count = sum(1 for r in results if r.tlc_pass)
        pass_k1_count = sum(1 for r in results if r.pass_rate_k1)
        
        codebleu_scores = [r.codebleu_score for r in results if r.codebleu_score is not None]
        cyclomatic_scores = [r.cyclomatic_complexity for r in results if r.cyclomatic_complexity is not None]
        halstead_efforts = [r.halstead_effort for r in results if r.halstead_effort is not None]
        maintainability_scores = [r.maintainability_index for r in results if r.maintainability_index is not None]
        
        generation_times = [r.generation_time_s for r in results if r.generation_time_s > 0]
        
        aggregated = {
            "model_name": self.model_name,
            "total_specs": total,
            "sany_pass": sany_pass_count,
            "sany_rate": round(sany_pass_count / total, 4),
            "tlc_pass": tlc_pass_count,
            "tlc_rate": round(tlc_pass_count / total, 4),
            "pass_k1": pass_k1_count,
            "pass_k1_rate": round(pass_k1_count / total, 4),
            "metrics": {
                "codebleu": {
                    "count": len(codebleu_scores),
                    "mean": round(sum(codebleu_scores) / len(codebleu_scores), 4) if codebleu_scores else None,
                    "min": round(min(codebleu_scores), 4) if codebleu_scores else None,
                    "max": round(max(codebleu_scores), 4) if codebleu_scores else None,
                },
                "cyclomatic_complexity": {
                    "count": len(cyclomatic_scores),
                    "mean": round(sum(cyclomatic_scores) / len(cyclomatic_scores), 2) if cyclomatic_scores else None,
                    "min": min(cyclomatic_scores) if cyclomatic_scores else None,
                    "max": max(cyclomatic_scores) if cyclomatic_scores else None,
                },
                "halstead_effort": {
                    "count": len(halstead_efforts),
                    "mean": round(sum(halstead_efforts) / len(halstead_efforts), 2) if halstead_efforts else None,
                    "min": round(min(halstead_efforts), 2) if halstead_efforts else None,
                    "max": round(max(halstead_efforts), 2) if halstead_efforts else None,
                },
                "maintainability_index": {
                    "count": len(maintainability_scores),
                    "mean": round(sum(maintainability_scores) / len(maintainability_scores), 2) if maintainability_scores else None,
                    "min": round(min(maintainability_scores), 2) if maintainability_scores else None,
                    "max": round(max(maintainability_scores), 2) if maintainability_scores else None,
                },
            },
            "generation": {
                "avg_time_s": round(sum(generation_times) / len(generation_times), 2) if generation_times else None,
                "min_time_s": round(min(generation_times), 2) if generation_times else None,
                "max_time_s": round(max(generation_times), 2) if generation_times else None,
            },
            "detailed_results": [asdict(r) for r in results],
        }
        
        return aggregated


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Test DPO-trained Spec-Align model")
    parser.add_argument(
        "--model-checkpoint",
        required=True,
        help="Path to fine-tuned model checkpoint",
    )
    parser.add_argument(
        "--model-name",
        default="spec-align",
        help="Model name for reporting",
    )
    parser.add_argument(
        "--spec-id",
        type=int,
        help="Test on single spec (if not provided, tests on entire test set)",
    )
    parser.add_argument(
        "--num-attempts",
        type=int,
        default=3,
        help="Number of generation attempts per spec",
    )
    parser.add_argument(
        "--temperature",
        type=float,
        default=0.7,
        help="Sampling temperature for generation",
    )
    parser.add_argument(
        "--output",
        default="outputs/dpo_model_test_results.json",
        help="Output file for results",
    )
    parser.add_argument("--wandb-project", default="tla_bench", help="W&B project name")
    parser.add_argument("--wandb-entity", default=None, help="W&B entity (team/user)")

    args = parser.parse_args()

    tester = DPOModelTester(
        model_checkpoint=args.model_checkpoint,
        model_name=args.model_name,
        wandb_project=args.wandb_project,
        wandb_entity=args.wandb_entity,
    )
    
    if args.spec_id:
        results = tester.test_on_spec(
            spec_id=args.spec_id,
            num_attempts=args.num_attempts,
            temperature=args.temperature,
        )
        output_data = {
            "single_spec_test": True,
            "spec_id": args.spec_id,
            "results": [asdict(r) for r in results],
        }
    else:
        output_data = tester.test_on_test_set(
            num_attempts=args.num_attempts,
            temperature=args.temperature,
        )
        output_data["full_test_set"] = True
    
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    save_json(output_data, output_path)
    
    logger.info(f"Test results saved to {output_path}")
    
    print(json.dumps(output_data, indent=2))


if __name__ == "__main__":
    main()
