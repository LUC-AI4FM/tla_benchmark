from __future__ import annotations

import json
import os
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import data_dir, get_ast_spec_by_id, get_logger, load_json, load_text, outputs_dir, repo_root, save_json
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
    pass_at_1: bool
    codebleu_score: float | None
    cyclomatic_complexity: float | None
    halstead_effort: float | None
    maintainability_index: float | None
    error: str | None = None


class DPOModelTester:
    def __init__(
        self,
        model_checkpoint: str,
        model_name: str = "spec-prover",
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

    def _load_model(self) -> None:
        cfg_file = Path(self.model_checkpoint) / "config.json"
        if cfg_file.exists():
            try:
                cfg = json.loads(cfg_file.read_text())
                if cfg.get("source") == "ollama_local":
                    self.backend = "ollama"
                    self._ollama_model = cfg.get("model_name", "deepseek-r1:8b")
                    logger.info("ollama backend: model=%s", self._ollama_model)
                    return
            except Exception:
                pass

        if self.backend == "huggingface":
            from transformers import AutoModelForCausalLM, AutoTokenizer
            logger.info("loading model from %s", self.model_checkpoint)
            self.tokenizer = AutoTokenizer.from_pretrained(self.model_checkpoint)
            self.model = AutoModelForCausalLM.from_pretrained(
                self.model_checkpoint,
                torch_dtype="auto",
                device_map="auto",
            )
            logger.info("model loaded: %s", self.model_checkpoint)

    def _generate(self, prompt: str, max_tokens: int = 8192, temperature: float = 0.7) -> tuple[str | None, float]:
        t0 = time.time()
        try:
            if self.backend == "ollama":
                import requests
                resp = requests.post(
                    "http://localhost:11434/api/generate",
                    json={
                        "model": self._ollama_model,
                        "prompt": prompt,
                        "stream": False,
                        "options": {"temperature": temperature, "num_predict": max_tokens},
                    },
                    timeout=300,
                )
                resp.raise_for_status()
                data = resp.json()
                # deepseek-r1: chain of thought is in "thinking", final answer in "response"
                thinking = data.get("thinking", "") or ""
                response = data.get("response", "") or ""
                text = (thinking + "\n" + response).strip() if thinking else response
            else:
                inputs = self.tokenizer(prompt, return_tensors="pt").to(self.model.device)
                out = self.model.generate(
                    **inputs,
                    max_new_tokens=max_tokens,
                    temperature=temperature,
                    top_p=0.95,
                    do_sample=True,
                    pad_token_id=self.tokenizer.eos_token_id,
                )
                text = self.tokenizer.decode(out[0], skip_special_tokens=True)

            elapsed = time.time() - t0
            tla = extract_tla_from_response(text)
            return tla, elapsed

        except Exception as exc:
            logger.error("generation error: %s", exc)
            return None, time.time() - t0

    def _build_prompt(self, spec_id: int) -> str | None:
        for ext in (".txt", ".json"):
            p = data_dir() / "descriptions" / f"{spec_id}{ext}"
            if p.exists():
                desc_text = p.read_text() if ext == ".txt" else json.dumps(load_json(p))
                break
        else:
            logger.warning("spec=%d: no description file", spec_id)
            return None

        template_path = repo_root() / "configs" / "prompts" / "nlp_to_tla.txt"
        if template_path.exists():
            return load_text(template_path).replace("{description}", desc_text)
        return desc_text

    def _validate(self, tla: str, spec_id: int, attempt: int) -> tuple[bool, bool]:
        tmp_dir = outputs_dir() / "temp"
        tmp_dir.mkdir(parents=True, exist_ok=True)
        tmp = tmp_dir / f"{spec_id}_attempt_{attempt}.tla"
        tmp.write_text(tla)
        cfg_path = data_dir() / "cfg" / f"{spec_id}.cfg"
        try:
            r = validate_spec(
                str(tmp),
                str(cfg_path) if cfg_path.exists() else None,
                str(tmp_dir),
                spec_id,
                self.model_name,
                "nlp_to_tla",
            )
            return r.get("sany_pass", False), r.get("tlc_pass", False)
        except Exception as exc:
            logger.error("spec=%d validation error: %s", spec_id, exc)
            return False, False
        finally:
            tmp.unlink(missing_ok=True)

    def test_spec(self, spec_id: int, num_attempts: int = 1, temperature: float = 0.7) -> list[ModelTestResult]:
        prompt = self._build_prompt(spec_id)
        if prompt is None:
            return []

        reference_ast = get_ast_spec_by_id(spec_id)
        results = []

        for attempt in range(num_attempts):
            tla, gen_time = self._generate(prompt, temperature=temperature)

            sany_pass, tlc_pass = (False, False)
            if tla:
                sany_pass, tlc_pass = self._validate(tla, spec_id, attempt)

            codebleu = cyclomatic = halstead = mi = None
            if tla:
                if reference_ast:
                    try:
                        codebleu = compute_codebleu(tla, reference_ast, spec_id)
                    except Exception:
                        pass
                try:
                    cyclomatic = compute_cyclomatic_complexity(tla)
                    h = compute_halstead_metrics(tla)
                    halstead = h.get("effort")
                    mi = compute_maintainability_index(tla)
                except Exception:
                    pass

            results.append(ModelTestResult(
                spec_id=spec_id,
                model_name=self.model_name,
                condition="nlp_to_tla",
                generated_tla=tla,
                generation_time_s=round(gen_time, 3),
                sany_pass=sany_pass,
                tlc_pass=tlc_pass,
                pass_at_1=(sany_pass and tlc_pass),
                codebleu_score=codebleu,
                cyclomatic_complexity=cyclomatic,
                halstead_effort=halstead,
                maintainability_index=mi,
            ))
            logger.info(
                "spec=%d attempt=%d/%d sany=%s tlc=%s time=%.2fs",
                spec_id, attempt + 1, num_attempts, sany_pass, tlc_pass, gen_time,
            )

        return results

    def test_on_test_set(
        self,
        output_file: str,
        test_ids: list[int] | None = None,
        num_attempts: int = 3,
        temperature: float = 0.7,
        limit: int | None = None,
    ) -> dict[str, Any]:
        if test_ids is None:
            split = data_dir() / "test_split.json"
            if not split.exists():
                logger.error("test_split.json not found")
                return {}
            test_ids = load_json(split).get("test_ids", [])

        if limit:
            test_ids = test_ids[:limit]

        use_wandb = False
        _run = None
        try:
            import wandb
            _run = wandb.init(
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
                },
            )
            use_wandb = True
        except Exception:
            pass

        all_results: list[ModelTestResult] = []
        step = 0

        for spec_id in test_ids:
            try:
                batch = self.test_spec(spec_id, num_attempts=num_attempts, temperature=temperature)
                all_results.extend(batch)
                if use_wandb:
                    for r in batch:
                        step += 1
                        import wandb as _wandb
                        _wandb.log({
                            "spec/sany_pass": int(r.sany_pass),
                            "spec/tlc_pass": int(r.tlc_pass),
                            "spec/pass_at_1": int(r.pass_at_1),
                            "spec/generation_time_s": r.generation_time_s,
                        }, step=step)
            except Exception as exc:
                logger.error("spec=%d: %s", spec_id, exc)
                all_results.append(ModelTestResult(
                    spec_id=spec_id, model_name=self.model_name, condition="nlp_to_tla",
                    generated_tla=None, generation_time_s=0.0,
                    sany_pass=False, tlc_pass=False, pass_at_1=False,
                    codebleu_score=None, cyclomatic_complexity=None,
                    halstead_effort=None, maintainability_index=None,
                    error=str(exc),
                ))

        result = self._aggregate(all_results)

        out = Path(output_file)
        out.parent.mkdir(parents=True, exist_ok=True)
        save_json(result, out)
        logger.info("saved: %s", out)

        if use_wandb and _run:
            import wandb as _wandb
            _wandb.summary.update({
                "test/sany_rate": result.get("sany_rate", 0),
                "test/tlc_rate": result.get("tlc_rate", 0),
                "test/pass_at_1_rate": result.get("pass_at_1_rate", 0),
            })
            _run.finish()

        return result

    def _aggregate(self, results: list[ModelTestResult]) -> dict[str, Any]:
        if not results:
            return {}

        n = len(results)
        sany = sum(1 for r in results if r.sany_pass)
        tlc = sum(1 for r in results if r.tlc_pass)
        p1 = sum(1 for r in results if r.pass_at_1)

        cb = [r.codebleu_score for r in results if r.codebleu_score is not None]
        cy = [r.cyclomatic_complexity for r in results if r.cyclomatic_complexity is not None]
        he = [r.halstead_effort for r in results if r.halstead_effort is not None]
        mi = [r.maintainability_index for r in results if r.maintainability_index is not None]
        gt = [r.generation_time_s for r in results if r.generation_time_s > 0]

        def _stats(vals: list) -> dict:
            if not vals:
                return {"count": 0, "mean": None, "min": None, "max": None}
            return {
                "count": len(vals),
                "mean": round(sum(vals) / len(vals), 4),
                "min": round(min(vals), 4),
                "max": round(max(vals), 4),
            }

        logger.info(
            "model=%s total=%d sany_rate=%.3f tlc_rate=%.3f pass_at_1_rate=%.3f",
            self.model_name, n, sany / n, tlc / n, p1 / n,
        )

        return {
            "model_name": self.model_name,
            "total_specs": n,
            "sany_pass": sany,
            "sany_rate": round(sany / n, 4),
            "tlc_pass": tlc,
            "tlc_rate": round(tlc / n, 4),
            "pass_at_1": p1,
            "pass_at_1_rate": round(p1 / n, 4),
            "metrics": {
                "codebleu": _stats(cb),
                "cyclomatic_complexity": _stats(cy),
                "halstead_effort": _stats(he),
                "maintainability_index": _stats(mi),
                "generation_time_s": _stats(gt),
            },
            "detailed_results": [asdict(r) for r in results],
        }


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--model-checkpoint", required=True)
    parser.add_argument("--model-name", default="spec-prover")
    parser.add_argument("--spec-id", type=int, default=None)
    parser.add_argument("--num-attempts", type=int, default=3)
    parser.add_argument("--temperature", type=float, default=0.7)
    parser.add_argument("--output", default="outputs/results/spec_prover_results.json")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--wandb-project", default="tla_bench")
    parser.add_argument("--wandb-entity", default=None)
    args = parser.parse_args()

    tester = DPOModelTester(
        model_checkpoint=args.model_checkpoint,
        model_name=args.model_name,
        wandb_project=args.wandb_project,
        wandb_entity=args.wandb_entity,
    )

    if args.spec_id is not None:
        results = tester.test_spec(spec_id=args.spec_id, num_attempts=args.num_attempts, temperature=args.temperature)
        out = {"spec_id": args.spec_id, "results": [asdict(r) for r in results]}
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        save_json(out, out_path)
        logger.info("saved: %s", out_path)
    else:
        tester.test_on_test_set(
            output_file=args.output,
            num_attempts=args.num_attempts,
            temperature=args.temperature,
            limit=args.limit,
        )


if __name__ == "__main__":
    main()
