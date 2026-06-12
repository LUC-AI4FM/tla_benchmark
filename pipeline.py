#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).parent
sys.path.insert(0, str(REPO_ROOT / "src"))

from utils import data_dir, get_logger, load_json, outputs_dir, repo_root, save_json

logger = get_logger("pipeline")

BASELINE_MODELS = [
    "qwen2.5-coder-14b",
    "deepseek-coder-v2",
    "qwen3.6-27b",
    "qwen3-coder-30b",
]
ALL_CONDITIONS = ["nlp_to_tla", "v2_to_tla", "v3_to_tla", "nlp_v3_to_tla"]


def step_baselines(
    models: list[str],
    limit: int | None,
    conditions: list[str],
    workers: int,
    resume: bool,
    use_wandb: bool,
) -> None:
    from runner import run_all

    models_cfg: list[dict] = load_json(repo_root() / "configs/models.json")
    split = load_json(data_dir() / "test_split.json")
    test_ids: list[int] = split["test_ids"]
    if limit:
        test_ids = test_ids[:limit]

    for model_cfg in models_cfg:
        if model_cfg["id"] not in models:
            continue
        try:
            results = run_all(
                model_cfg, test_ids, conditions,
                workers=workers, resume=resume, use_wandb=use_wandb,
            )
            out = outputs_dir() / f"run_{model_cfg['id']}.json"
            save_json(results, out)
        except Exception as exc:
            logger.error("baseline run failed for %s: %s", model_cfg["id"], exc, exc_info=True)


def step_hivemind(condition: str | None) -> None:
    from hivemind import run_analysis

    out_path = outputs_dir() / "results" / "hivemind.json"
    try:
        run_analysis(condition=condition, out_path=out_path)
    except RuntimeError as exc:
        logger.warning("hivemind skipped: %s", exc)
    except Exception as exc:
        logger.error("hivemind failed: %s", exc, exc_info=True)


def step_preference_gen(
    model: str,
    limit: int | None,
    num_candidates: int,
    output_path: Path | None,
) -> None:
    from preference_generator import generate_preference_dataset

    split = load_json(data_dir() / "test_split.json")
    spec_ids: list[int] = split["train_ids"]
    if limit:
        spec_ids = spec_ids[:limit]

    models_cfg: list[dict] = load_json(repo_root() / "configs/models.json")
    matched = [m for m in models_cfg if m["id"] == model]
    if matched:
        model_cfg = dict(matched[0])
        model_cfg.setdefault("temperature", 0.7)
        model_cfg.setdefault("max_tokens", 4096)
    else:
        model_cfg = {
            "id": model,
            "backend": "ollama",
            "model_name": model,
            "temperature": 0.7,
            "max_tokens": 4096,
        }
    out = output_path or outputs_dir() / "preference_dataset.jsonl"
    try:
        generate_preference_dataset(
            spec_ids=spec_ids,
            model_config=model_cfg,
            num_candidates=num_candidates,
            output_path=out,
        )
    except Exception as exc:
        logger.error("preference generation failed: %s", exc, exc_info=True)


def step_train_dpo(
    base_model: str,
    train_path: Path | None,
    eval_path: Path | None,
    use_wandb: bool,
) -> None:
    from dpo_trainer import train_dpo_model

    train_file = train_path or outputs_dir() / "preference_dataset.jsonl"
    if not train_file.exists():
        logger.error("train file not found: %s", train_file)
        return
    out_dir = outputs_dir() / "dpo_models"
    try:
        train_dpo_model(
            base_model=base_model,
            train_dataset_path=train_file,
            eval_dataset_path=eval_path,
            output_dir=out_dir,
            wandb_project="tla_bench",
        )
    except Exception as exc:
        logger.error("dpo training failed: %s", exc, exc_info=True)


def step_train_sft(
    base_model: str,
    train_path: Path | None,
    eval_path: Path | None,
    use_wandb: bool,
) -> None:
    from sft_trainer import train_sft_model

    train_file = train_path or outputs_dir() / "sft_dataset.jsonl"
    if not train_file.exists():
        logger.error("train file not found: %s", train_file)
        return
    out_dir = outputs_dir() / "sft_models"
    try:
        train_sft_model(
            base_model=base_model,
            train_dataset_path=train_file,
            eval_dataset_path=eval_path,
            output_dir=out_dir,
            wandb_project="tla_bench",
        )
    except Exception as exc:
        logger.error("sft training failed: %s", exc, exc_info=True)


def step_spec_prover(checkpoint: str | None, limit: int | None) -> None:
    from dpo_model_tester import DPOModelTester

    if checkpoint is None:
        default = outputs_dir() / "dpo_models" / "final_model"
        if default.exists():
            checkpoint = str(default)
        else:
            logger.error("no checkpoint found, pass --checkpoint or train first")
            return

    out_file = str(outputs_dir() / "results" / "spec_prover_results.json")
    try:
        tester = DPOModelTester(model_checkpoint=checkpoint, model_name="spec-prover")
        tester.test_on_test_set(output_file=out_file, num_attempts=3, limit=limit)
    except Exception as exc:
        logger.error("spec-prover evaluation failed: %s", exc, exc_info=True)


def step_analysis(use_wandb: bool) -> None:
    import importlib
    for name, module_name in [("dataset", "analyze_dataset"), ("results", "analyze_results")]:
        try:
            mod = importlib.import_module(module_name)
            mod.run_analysis(use_wandb=use_wandb)
        except RuntimeError as exc:
            logger.warning("%s analysis skipped: %s", name, exc)
        except Exception as exc:
            logger.error("%s analysis failed: %s", name, exc, exc_info=True)


def print_summary(models: list[str]) -> None:
    rows = []
    for model in models:
        rf = outputs_dir() / f"run_{model}.json"
        if not rf.exists():
            continue
        data = load_json(rf)
        n = len(data)
        if n == 0:
            continue
        rows.append((
            model, n,
            sum(1 for r in data if r.get("sany_pass")) / n,
            sum(1 for r in data if r.get("tlc_pass")) / n,
            sum(1 for r in data if r.get("pass_at_1")) / n,
        ))

    sp_file = outputs_dir() / "results" / "spec_prover_results.json"
    if sp_file.exists():
        data = load_json(sp_file)
        if isinstance(data, dict):
            n = data.get("total_specs", 0)
            if n:
                rows.append((
                    "spec-prover (dpo)", n,
                    data.get("sany_rate", 0),
                    data.get("tlc_rate", 0),
                    data.get("pass_at_1_rate", 0),
                ))

    if not rows:
        return

    print(f"{'model':<28} {'n':>5}  {'sany':>6}  {'tlc':>6}  {'pass@1':>7}")
    print("-" * 56)
    for name, n, sany, tlc, p1 in rows:
        print(f"{name:<28} {n:>5}  {sany:>6.3f}  {tlc:>6.3f}  {p1:>7.3f}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--step", choices=[
        "baselines", "hivemind", "preference-gen",
        "train-dpo", "train-sft", "spec-prover", "analysis",
    ])
    parser.add_argument("--model", default=None)
    parser.add_argument("--base-model", default=None, help="base model for dpo/sft training")
    parser.add_argument("--condition", default=None, choices=ALL_CONDITIONS)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--no-wandb", action="store_true")
    parser.add_argument("--checkpoint", default=None)
    parser.add_argument("--train-file", type=Path, default=None)
    parser.add_argument("--eval-file", type=Path, default=None)
    parser.add_argument("--candidates", type=int, default=5, help="candidates per spec for preference-gen")
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()

    models = [args.model] if args.model else BASELINE_MODELS
    conditions = [args.condition] if args.condition else ALL_CONDITIONS
    use_wandb = not args.no_wandb

    t0 = time.time()

    if args.step == "baselines":
        step_baselines(models, args.limit, conditions, args.workers, args.resume, use_wandb)

    elif args.step == "hivemind":
        step_hivemind(args.condition)

    elif args.step == "preference-gen":
        gen_model = args.model or "qwen2.5-coder:32b"
        step_preference_gen(gen_model, args.limit, args.candidates, args.output)

    elif args.step == "train-dpo":
        if not args.base_model:
            logger.error("--base-model required for train-dpo")
            sys.exit(1)
        step_train_dpo(args.base_model, args.train_file, args.eval_file, use_wandb)

    elif args.step == "train-sft":
        if not args.base_model:
            logger.error("--base-model required for train-sft")
            sys.exit(1)
        step_train_sft(args.base_model, args.train_file, args.eval_file, use_wandb)

    elif args.step == "spec-prover":
        step_spec_prover(args.checkpoint, args.limit)

    elif args.step == "analysis":
        step_analysis(use_wandb)

    else:
        step_baselines(models, args.limit, conditions, args.workers, args.resume, use_wandb)
        step_hivemind(args.condition)
        step_spec_prover(args.checkpoint, args.limit)
        step_analysis(use_wandb)
        print_summary(models)

    logger.info("done in %.0fs", time.time() - t0)


if __name__ == "__main__":
    main()
