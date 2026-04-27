from __future__ import annotations

import argparse
import csv
import math
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import (
    data_dir, get_logger, load_json, outputs_dir,
    repo_root, results_dir, save_json,
)

logger = get_logger("metrics")

CONDITIONS: list[str] = ["nlp_to_tla", "v2_to_tla", "v3_to_tla", "ast_to_tla"]


def pass_at_k(n: int, c: int, k: int) -> float:
    if n - c < k:
        return 1.0
    if n == 0 or k == 0:
        return 0.0

    log_prod = 0.0
    for i in range(k):
        log_prod += math.log(n - c - i) - math.log(n - i)

    return 1.0 - math.exp(log_prod)


def _collect_summaries() -> list[dict[str, Any]]:
    validation_base = outputs_dir() / "validation"
    if not validation_base.exists():
        return []

    summaries: list[dict[str, Any]] = []

    for model_dir in sorted(validation_base.iterdir()):
        if not model_dir.is_dir():
            continue
        for cond_dir in sorted(model_dir.iterdir()):
            if not cond_dir.is_dir():
                continue
            for spec_dir in sorted(cond_dir.iterdir()):
                if not spec_dir.is_dir():
                    continue
                for summary_file in sorted(spec_dir.glob("*_summary.json")):
                    try:
                        summaries.append(load_json(summary_file))
                    except Exception as exc:
                        logger.warning("Failed to load %s: %s", summary_file, exc)

    logger.info("collected %d sample summaries", len(summaries))
    return summaries


def compute_summary(summaries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    groups: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for s in summaries:
        key = (s.get("model_id", "unknown"), s.get("condition", "unknown"))
        groups[key].append(s)

    rows: list[dict[str, Any]] = []
    for (model_id, condition), samples in sorted(groups.items()):
        total = len(samples)
        sany_pass = sum(1 for s in samples if s.get("sany_pass", False))
        tlc_pass = sum(1 for s in samples if s.get("tlc_pass", False))

        rows.append({
            "model_id": model_id, "condition": condition,
            "total_samples": total,
            "sany_pass": sany_pass,
            "sany_rate": round(sany_pass / total, 4) if total else 0.0,
            "tlc_pass": tlc_pass,
            "tlc_rate": round(tlc_pass / total, 4) if total else 0.0,
        })

    return rows


def compute_pass_at_k(
    summaries: list[dict[str, Any]],
    k_values: tuple[int, ...] = (1, 5, 10),
) -> list[dict[str, Any]]:
    spec_groups: dict[tuple[str, str, str], list[dict]] = defaultdict(list)
    for s in summaries:
        key = (
            s.get("model_id", "unknown"),
            s.get("condition", "unknown"),
            str(s.get("spec_id", "unknown")),
        )
        spec_groups[key].append(s)

    model_cond_groups: dict[tuple[str, str], list[tuple[int, int]]] = defaultdict(list)
    for (model_id, condition, spec_id), samples in spec_groups.items():
        n = len(samples)
        c = sum(1 for s in samples if s.get("tlc_pass", False))
        model_cond_groups[(model_id, condition)].append((n, c))

    rows: list[dict[str, Any]] = []
    for (model_id, condition), nc_pairs in sorted(model_cond_groups.items()):
        row: dict[str, Any] = {
            "model_id": model_id, "condition": condition,
            "num_specs": len(nc_pairs),
        }

        for k in k_values:
            scores = [pass_at_k(n, c, k) for n, c in nc_pairs]
            avg = sum(scores) / max(len(scores), 1)
            row[f"pass_at_{k}"] = round(avg, 4)

        rows.append(row)

    return rows


def compute_comparison(pass_at_k_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    model_scores: dict[str, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
    for row in pass_at_k_rows:
        mid = row["model_id"]
        for k in (1, 5, 10):
            col = f"pass_at_{k}"
            if col in row:
                model_scores[mid][col].append(row[col])

    comparison: list[dict[str, Any]] = []
    for model_id, scores in sorted(model_scores.items()):
        row: dict[str, Any] = {
            "model_id": model_id,
            "minif2f_pass_rate": None,
            "putnambench_pass_rate": None,
        }
        for col, values in scores.items():
            row[f"tlabench_{col}"] = round(sum(values) / len(values), 4) if values else None

        comparison.append(row)

    return comparison


def _write_csv(rows: list[dict[str, Any]], path: Path) -> None:
    if not rows:
        return

    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = list(rows[0].keys())

    with open(path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    logger.info("wrote %d rows to %s", len(rows), path)


def main() -> None:
    parser = argparse.ArgumentParser(description="TLA+Bench evaluation metrics.")
    parser.parse_args()

    summaries = _collect_summaries()
    if not summaries:
        logger.error("No summaries found. Run the evaluation pipeline first.")
        return

    baseline_dir = results_dir() / "baseline"

    summary_rows = compute_summary(summaries)
    _write_csv(summary_rows, baseline_dir / "summary.csv")

    pak_rows = compute_pass_at_k(summaries)
    _write_csv(pak_rows, baseline_dir / "pass_at_k.csv")

    comparison_rows = compute_comparison(pak_rows)
    _write_csv(comparison_rows, baseline_dir / "comparison.csv")

    for row in pak_rows:
        logger.info(
            "model=%-25s cond=%-12s Pass@1=%.2f%% Pass@5=%.2f%% Pass@10=%.2f%%",
            row["model_id"], row["condition"],
            row.get("pass_at_1", 0) * 100,
            row.get("pass_at_5", 0) * 100,
            row.get("pass_at_10", 0) * 100,
        )

    logger.info("metrics complete")


if __name__ == "__main__":
    main()
