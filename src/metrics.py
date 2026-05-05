from __future__ import annotations

import csv
import json
import os
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger, load_json, outputs_dir, repo_root, results_dir, save_json
from code_quality_metrics import compute_code_quality_metrics, compare_code_quality, extract_ast, codebleu_ast_similarity

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


def compute_code_quality_summary(model_id: str, condition: str) -> dict[str, Any]:
    validation_dir = outputs_dir() / "validation" / model_id / condition
    if not validation_dir.exists():
        return {}
    
    code_quality_metrics = []
    for f in sorted(validation_dir.glob("*_summary.json")):
        try:
            summary = load_json(f)
            if summary.get("sany_pass") and summary.get("tlc_pass"):
                tla_file = validation_dir / f"{summary.get('spec_id')}.tla"
                if tla_file.exists():
                    with open(tla_file, "r") as tf:
                        code = tf.read()
                    metrics = compute_code_quality_metrics(code)
                    code_quality_metrics.append(metrics)
        except Exception:
            pass
    
    if not code_quality_metrics:
        return {}
    
    avg_cc = sum(m["cyclomatic_complexity"] for m in code_quality_metrics) / len(code_quality_metrics)
    avg_mi = sum(m["maintainability_index"] for m in code_quality_metrics) / len(code_quality_metrics)
    avg_loc = sum(m["lines_of_code"] for m in code_quality_metrics) / len(code_quality_metrics)
    
    return {
        "num_valid_specs": len(code_quality_metrics),
        "avg_cyclomatic_complexity": round(avg_cc, 2),
        "avg_maintainability_index": round(avg_mi, 2),
        "avg_lines_of_code": round(avg_loc, 2),
    }


def compute_codebleu_score(model_id: str, condition: str) -> dict[str, Any]:
    validation_dir = outputs_dir() / "validation" / model_id / condition
    ast_dir = outputs_dir() / "ast_comparisons" / model_id / condition
    
    if not validation_dir.exists():
        return {}
    
    codebleu_scores = []
    for f in sorted(validation_dir.glob("*_summary.json")):
        try:
            summary = load_json(f)
            spec_id = summary.get("spec_id")
            
            if summary.get("sany_pass") and summary.get("tlc_pass"):
                gen_file = validation_dir / f"{spec_id}.tla"
                ref_file = outputs_dir() / "reference_tlas" / f"{spec_id}.tla"
                
                if gen_file.exists() and ref_file.exists():
                    with open(gen_file, "r") as f:
                        gen_code = f.read()
                    with open(ref_file, "r") as f:
                        ref_code = f.read()
                    
                    gen_ast = extract_ast(gen_code)
                    ref_ast = extract_ast(ref_code)
                    score = codebleu_ast_similarity(gen_ast, ref_ast)
                    codebleu_scores.append(score)
        except Exception:
            pass
    
    if not codebleu_scores:
        return {}
    
    avg_score = sum(codebleu_scores) / len(codebleu_scores)
    return {
        "num_comparisons": len(codebleu_scores),
        "avg_codebleu_score": round(avg_score, 4),
        "max_codebleu_score": round(max(codebleu_scores), 4),
        "min_codebleu_score": round(min(codebleu_scores), 4),
    }


def write_detailed_metrics_csv(model_id: str) -> None:
    results_dir().mkdir(parents=True, exist_ok=True)
    out_path = results_dir() / f"detailed_metrics_{model_id}.csv"
    
    rows = []
    for condition in CONDITIONS:
        code_quality = compute_code_quality_summary(model_id, condition)
        codebleu = compute_codebleu_score(model_id, condition)
        
        row = {
            "model_id": model_id,
            "condition": condition,
            **code_quality,
            **codebleu,
        }
        rows.append(row)
    
    if rows:
        fieldnames = list(rows[0].keys())
        with open(out_path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        logger.info("Wrote detailed metrics: %s", out_path)


def main():
    summary = compute_summary()
    write_summary_csv(summary)
    comparison = compute_comparison()
    write_comparison_csv(comparison)
    
    models_cfg = load_json(repo_root() / "configs/models.json")
    for model_cfg in models_cfg:
        write_detailed_metrics_csv(model_cfg["id"])
    
    logger.info("Metrics computation complete")


if __name__ == "__main__":
    main()
