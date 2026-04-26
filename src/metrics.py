from __future__ import annotations

import csv
import os
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger, load_json, outputs_dir, repo_root, results_dir, save_json

logger = get_logger("metrics")

CONDITIONS = ["nlp_to_tla", "v2_to_tla", "v3_to_tla"]


def _collect_results(model_id: str, condition: str) -> list[dict[str, Any]]:
    validation_dir = outputs_dir() / "validation" / model_id / condition
    if not validation_dir.exists():
        return []
    summaries = []
    for f in sorted(validation_dir.glob("*_summary.json")):
        try:
            summaries.append(load_json(f))
        except Exception:
            pass
    return summaries


def compute_summary() -> list[dict[str, Any]]:
    models_cfg = load_json(repo_root() / "configs/models.json")
    rows = []
    for model_cfg in models_cfg:
        model_id = model_cfg["id"]
        for condition in CONDITIONS:
            summaries = _collect_results(model_id, condition)
            if not summaries:
                continue
            total = len(summaries)
            sany_pass = sum(1 for s in summaries if s.get("sany_pass", False))
            tlc_pass = sum(1 for s in summaries if s.get("tlc_pass", False))
            rows.append({
                "model_id": model_id,
                "condition": condition,
                "total_specs": total,
                "sany_pass": sany_pass,
                "sany_rate": round(sany_pass / total, 4) if total else 0.0,
                "tlc_pass": tlc_pass,
                "tlc_rate": round(tlc_pass / total, 4) if total else 0.0,
            })
    return rows


def write_summary_csv(rows: list[dict[str, Any]]) -> None:
    results_dir().mkdir(parents=True, exist_ok=True)
    out_path = results_dir() / "summary.csv"
    fieldnames = ["model_id", "condition", "total_specs", "sany_pass", "sany_rate", "tlc_pass", "tlc_rate"]
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    logger.info("Wrote summary.csv: %d rows", len(rows))


def compute_comparison() -> list[dict[str, Any]]:
    summary_rows = compute_summary()

    rates = {
        cond: {r["model_id"]: r["tlc_rate"] for r in summary_rows if r["condition"] == cond}
        for cond in CONDITIONS
    }

    models_cfg = load_json(repo_root() / "configs/models.json")
    comparison = []
    for model_cfg in models_cfg:
        mid = model_cfg["id"]
        comparison.append({
            "model_id": mid,
            "minif2f_pass_rate": None,
            "putnambench_pass_rate": None,
            "tlabench_nlp_rate": rates["nlp_to_tla"].get(mid),
            "tlabench_v2_rate": rates["v2_to_tla"].get(mid),
            "tlabench_v3_rate": rates["v3_to_tla"].get(mid),
        })
    return comparison


def write_comparison_csv(rows: list[dict[str, Any]]) -> None:
    results_dir().mkdir(parents=True, exist_ok=True)
    out_path = results_dir() / "comparison.csv"
    fieldnames = [
        "model_id", "minif2f_pass_rate", "putnambench_pass_rate",
        "tlabench_nlp_rate", "tlabench_v2_rate", "tlabench_v3_rate",
    ]
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    logger.info("Wrote comparison.csv: %d rows", len(rows))


def main():
    summary = compute_summary()
    write_summary_csv(summary)
    comparison = compute_comparison()
    write_comparison_csv(comparison)
    logger.info("Metrics computation complete")


if __name__ == "__main__":
    main()
