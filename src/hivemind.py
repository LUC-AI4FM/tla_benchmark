#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))
from utils import get_logger, outputs_dir

logger = get_logger("hivemind")

# error taxonomy (sany=syntactic, tlc=semantic)
S_CATEGORIES = {
    "S1": "unicode_operator_substitution",        # ∧ ∨ ∀ ∃ instead of /\ \/ \A \E
    "S2": "cross_language_syntax_injection",      # { } ; from python/java
    "S3": "reasoning_formatting_leakage",         # <think> tags left in output
    "S4": "generation_length_miscalibration",     # truncated / empty output
}
E_CATEGORIES = {
    "E1": "structural_error_missing_footer",      # missing ==== footer
    "E2": "structural_error_duplicate_module",    # module declaration repeated
    "E3": "extraction_failed",                    # no module block found in output
    "E4": "sany_failed_no_category",             # sany failed, category not above
}

BASELINE_MODELS = ["deepseek-r1-8b", "deepseek-r1-32b", "qwen2.5-coder-32b", "llama3.3-70b"]


def load_run(model: str, condition: str | None) -> list[dict]:
    rf = outputs_dir() / f"run_{model}.json"
    if not rf.exists():
        return []
    data = json.loads(rf.read_text())
    if condition:
        data = [r for r in data if r.get("condition") == condition]
    return data


def load_error_taxonomy(model: str, condition: str | None) -> dict[int, dict]:
    val_dir = outputs_dir() / "validation" / model
    if not val_dir.exists():
        return {}

    result = {}
    cond_dirs = [val_dir / condition] if condition else list(val_dir.iterdir())
    for cond_dir in cond_dirs:
        if not cond_dir.is_dir():
            continue
        for ef in cond_dir.glob("*_errors.json"):
            spec_id = int(ef.stem.replace("_errors", ""))
            result[spec_id] = json.loads(ef.read_text())
    return result


def classify_run_record(rec: dict, error_tax: dict) -> dict[str, bool]:
    spec_id = rec.get("spec_id")
    if rec.get("error") == "extraction_failed":
        return {**{v: False for v in S_CATEGORIES.values()},
                "structural_error_missing_footer": False,
                "structural_error_duplicate_module": False,
                "extraction_failed": True,
                "sany_failed_no_category": False}

    cats = error_tax.get(spec_id, {})
    has_any = any(cats.values()) if cats else False
    return {**cats,
            "extraction_failed": False,
            "sany_failed_no_category": not has_any and not rec.get("sany_pass", False)}


def compute_hivemind(model_failures: dict[str, set], all_spec_ids: set) -> dict:
    models = [m for m in model_failures if model_failures[m]]
    if not models:
        return {"H": None, "H_ind": None, "ratio": None,
                "n_intersection": 0, "n_union": 0, "note": "no failure data"}

    if len(models) == 1:
        f = model_failures[models[0]]
        return {"H": 1.0, "H_ind": 1.0, "ratio": 1.0,
                "n_intersection": len(f), "n_union": len(f),
                "note": "only one model - Hivemind requires ≥2"}

    intersection = set.intersection(*[model_failures[m] for m in models])
    union = set.union(*[model_failures[m] for m in models])
    H = len(intersection) / len(union) if union else 0.0

    # expected H under independence: product of per model failure rates over union
    H_ind = 1.0
    for m in models:
        rate = len(model_failures[m]) / len(union)
        H_ind *= rate

    ratio = H / H_ind if H_ind > 0 else float("inf")

    note = ""
    if len(union) == len(intersection):
        note = "H=1: all models fail all specs - need partial passes for meaningful analysis"
    elif H_ind == 0:
        note = "H_ind=0: some models have zero failures"

    return {
        "H": round(H, 4),
        "H_ind": round(H_ind, 4),
        "ratio": round(ratio, 2),
        "n_intersection": len(intersection),
        "n_union": len(union),
        "intersection_spec_ids": sorted(intersection),
        "note": note,
    }


def aggregate_taxonomy(all_cats: list[dict]) -> dict:
    total = len(all_cats)
    if total == 0:
        return {}
    counts = Counter()
    for cats in all_cats:
        for k, v in cats.items():
            if v:
                counts[k] += 1
    return {k: {"count": v, "pct": round(100 * v / total, 1)} for k, v in counts.most_common()}


def run_analysis(
    condition: str | None = None,
    models: list[str] | None = None,
    out_path: Path | None = None,
) -> dict:
    if out_path is None:
        out_path = outputs_dir() / "results" / "hivemind.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)

    model_list = models if models else BASELINE_MODELS

    model_data = {}
    for model in model_list:
        records = load_run(model, condition)
        if not records:
            logger.warning("No run file for model %s - skipping", model)
            continue
        error_tax = load_error_taxonomy(model, condition)
        model_data[model] = {"records": records, "error_tax": error_tax}

    if not model_data:
        raise RuntimeError("No run files found. Run baselines first.")

    model_failures: dict[str, set] = {}
    model_taxonomy: dict[str, dict] = {}
    all_spec_ids: set = set()

    for model, d in model_data.items():
        failed: set = set()
        cats_list = []
        for rec in d["records"]:
            all_spec_ids.add(rec["spec_id"])
            if not rec.get("sany_pass", False):
                failed.add(rec["spec_id"])
                cats_list.append(classify_run_record(rec, d["error_tax"]))
        model_failures[model] = failed
        model_taxonomy[model] = aggregate_taxonomy(cats_list)

    hivemind = compute_hivemind(model_failures, all_spec_ids)

    all_cats = []
    for model, d in model_data.items():
        for rec in d["records"]:
            if not rec.get("sany_pass", False):
                all_cats.append(classify_run_record(rec, d["error_tax"]))
    aggregate_tax = aggregate_taxonomy(all_cats)

    per_model = {}
    for model, d in model_data.items():
        total = len(d["records"])
        passed = sum(1 for r in d["records"] if r.get("sany_pass"))
        per_model[model] = {
            "total_specs": total,
            "sany_pass": passed,
            "sany_fail": total - passed,
            "sany_rate": round(passed / total, 4) if total else 0,
            "error_taxonomy": model_taxonomy[model],
        }

    result = {
        "condition": condition or "all",
        "models_analyzed": list(model_data.keys()),
        "hivemind_index": hivemind,
        "per_model": per_model,
        "aggregate_error_taxonomy": aggregate_tax,
    }

    with open(out_path, "w") as f:
        json.dump(result, f, indent=2)

    logger.info("saved: %s", out_path)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description="Logical Hivemind cross-model failure analysis")
    parser.add_argument("--condition", default=None, choices=["nlp_to_tla", "v2_to_tla", "v3_to_tla", "nlp_v2_to_tla", "nlp_v3_to_tla"])
    parser.add_argument("--models", default=None, help="Comma-separated model ids")
    parser.add_argument("--out", default=None, help="Output JSON path")
    args = parser.parse_args()

    out_path = Path(args.out) if args.out else None
    models = args.models.split(",") if args.models else None
    try:
        run_analysis(condition=args.condition, models=models, out_path=out_path)
    except RuntimeError as e:
        logger.error("%s", e)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
