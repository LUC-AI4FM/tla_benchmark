#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import sys
from collections import defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from utils import data_dir, get_logger, load_json, outputs_dir, repo_root

logger = get_logger("analyze_results")

BASELINE_MODELS = ["deepseek-r1-8b", "deepseek-r1-32b", "qwen2.5-coder-32b", "llama3.3-70b"]
CONDITIONS = ["nlp_to_tla", "v2_to_tla", "v3_to_tla", "nlp_v2_to_tla", "nlp_v3_to_tla"]
TIERS = ["basic", "intermediate", "advanced", "auxiliary"]


def load_run(model: str) -> list[dict]:
    rf = outputs_dir() / f"run_{model}.json"
    if not rf.exists():
        return []
    return load_json(rf)


def load_spec_prover() -> list[dict]:
    rf = outputs_dir() / "results" / "spec_prover_results.json"
    if not rf.exists():
        return []
    data = load_json(rf)
    if isinstance(data, list):
        return data
    # summary only dict, reconstruct minimal record list
    total = data.get("total_specs", 0)
    n_sany = data.get("sany_pass", 0)
    n_tlc = data.get("tlc_pass", 0)
    records = []
    for i in range(total):
        records.append({
            "spec_id": i, "model_id": data.get("model_name", "spec-prover"),
            "condition": "nlp_to_tla",
            "sany_pass": i < n_sany, "tlc_pass": i < n_tlc,
            "pass_at_1": i < n_tlc,
        })
    return records


def pass_at_k_unbiased(n: int, c: int, k: int) -> float:
    if n == 0 or k > n:
        return 0.0
    if c == 0:
        return 0.0
    if n - c < k:
        return 1.0
    # Use log to avoid overflow
    log_num = sum(math.log(n - c - i) for i in range(k))
    log_den = sum(math.log(n - i) for i in range(k))
    return 1.0 - math.exp(log_num - log_den)


def bootstrap_ci(values: list[float], n_boot: int = 1000, ci: float = 0.95) -> tuple[float, float]:
    if not values:
        return (0.0, 0.0)
    arr = np.array(values, dtype=float)
    rng = np.random.default_rng(42)
    boot_means = [rng.choice(arr, size=len(arr), replace=True).mean() for _ in range(n_boot)]
    lo = (1 - ci) / 2
    hi = 1 - lo
    return (float(np.quantile(boot_means, lo)), float(np.quantile(boot_means, hi)))


def model_performance(records: list[dict]) -> dict:
    if not records:
        return {}

    overall = {"total": 0, "sany": 0, "tlc": 0, "pass1": 0}
    by_condition: dict[str, dict] = defaultdict(lambda: {"total": 0, "sany": 0, "tlc": 0, "pass1": 0})
    by_tier: dict[str, dict] = defaultdict(lambda: {"total": 0, "sany": 0, "tlc": 0, "pass1": 0})

    sany_flags, tlc_flags, pass1_flags = [], [], []

    for r in records:
        s = int(bool(r.get("sany_pass")))
        t = int(bool(r.get("tlc_pass")))
        p1 = int(bool(r.get("pass_at_1", r.get("sany_pass") and r.get("tlc_pass"))))
        cond = r.get("condition", "unknown")
        tier = r.get("complexity_tier", "unknown")

        overall["total"] += 1
        overall["sany"] += s
        overall["tlc"] += t
        overall["pass1"] += p1

        by_condition[cond]["total"] += 1
        by_condition[cond]["sany"] += s
        by_condition[cond]["tlc"] += t
        by_condition[cond]["pass1"] += p1

        by_tier[tier]["total"] += 1
        by_tier[tier]["sany"] += s
        by_tier[tier]["tlc"] += t
        by_tier[tier]["pass1"] += p1

        sany_flags.append(s)
        tlc_flags.append(t)
        pass1_flags.append(p1)

    def rates(stats):
        n = stats["total"]
        return {
            "n": n,
            "sany_rate": round(stats["sany"] / n, 4) if n else 0.0,
            "tlc_rate": round(stats["tlc"] / n, 4) if n else 0.0,
            "pass1_rate": round(stats["pass1"] / n, 4) if n else 0.0,
        }

    sany_ci = bootstrap_ci(sany_flags)
    pass1_ci = bootstrap_ci(pass1_flags)

    result = {
        "overall": {
            **rates(overall),
            "sany_ci_95": [round(sany_ci[0], 4), round(sany_ci[1], 4)],
            "pass1_ci_95": [round(pass1_ci[0], 4), round(pass1_ci[1], 4)],
        },
        "by_condition": {cond: rates(stats) for cond, stats in by_condition.items()},
        "by_tier": {tier: rates(stats) for tier, stats in by_tier.items()},
    }

    n_total = overall["total"]
    n_pass = overall["sany"]
    for k in (1, 3, 5, 10):
        result["overall"][f"pass_at_{k}_unbiased"] = round(pass_at_k_unbiased(n_total, n_pass, k), 4)

    return result


def error_taxonomy(model: str, records: list[dict], condition: str | None = None) -> dict:
    hm_file = outputs_dir() / "results" / "hivemind.json"
    if hm_file.exists():
        hm_data = load_json(hm_file)
        per_model = hm_data.get("per_model", {})
        if model in per_model:
            return per_model[model].get("error_taxonomy", {})
    return {}


def ranking_table(all_perf: dict[str, dict]) -> list[dict]:
    rows = []
    for model, perf in all_perf.items():
        ov = perf.get("overall", {})
        rows.append({
            "model": model,
            "n": ov.get("n", 0),
            "sany_rate": ov.get("sany_rate", 0.0),
            "tlc_rate": ov.get("tlc_rate", 0.0),
            "pass1_rate": ov.get("pass1_rate", 0.0),
            "pass_at_1_unbiased": ov.get("pass_at_1_unbiased", 0.0),
            "pass_at_3_unbiased": ov.get("pass_at_3_unbiased", 0.0),
            "pass_at_5_unbiased": ov.get("pass_at_5_unbiased", 0.0),
            "pass_at_10_unbiased": ov.get("pass_at_10_unbiased", 0.0),
        })
    return sorted(rows, key=lambda x: -x["sany_rate"])


def make_figures(all_perf: dict, ranking: list, out_dir: Path) -> list[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    saved = []

    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        logger.warning("matplotlib not available - skipping figures")
        return []

    models = [r["model"] for r in ranking]
    sany_rates = [r["sany_rate"] for r in ranking]
    tlc_rates = [r["tlc_rate"] for r in ranking]
    pass1_rates = [r["pass1_rate"] for r in ranking]

    # 1. overall sany vs tlc grouped bar
    x = np.arange(len(models))
    w = 0.3
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.bar(x - w / 2, sany_rates, w, label="SANY pass rate", color="#4C72B0")
    ax.bar(x + w / 2, tlc_rates, w, label="TLC pass rate", color="#DD8452")
    ax.set_xticks(x)
    ax.set_xticklabels(models, rotation=20, ha="right")
    ax.set_ylabel("Pass Rate")
    ax.set_title("Baseline Model Performance: SANY vs TLC")
    ax.set_ylim(0, 1.05)
    ax.legend()
    ax.axhline(0, color="black", linewidth=0.5)
    fig.tight_layout()
    p = out_dir / "model_sany_tlc.png"
    fig.savefig(str(p), dpi=150)
    plt.close(fig)
    saved.append(p)

    # 2. per condition breakdown for each model
    cond_colors = {"nlp_to_tla": "#4C72B0", "v2_to_tla": "#DD8452", "v3_to_tla": "#55A868",
                   "nlp_v2_to_tla": "#C44E52", "nlp_v3_to_tla": "#8172B2"}
    fig, axes = plt.subplots(1, len(all_perf), figsize=(4 * len(all_perf), 5), sharey=True)
    if len(all_perf) == 1:
        axes = [axes]
    for ax, (model, perf) in zip(axes, all_perf.items()):
        conds = perf.get("by_condition", {})
        c_names = list(conds.keys())
        sany_vals = [conds[c]["sany_rate"] for c in c_names]
        colors = [cond_colors.get(c, "#999") for c in c_names]
        ax.bar(c_names, sany_vals, color=colors)
        ax.set_title(model.replace("-", "\n"), fontsize=9)
        ax.set_ylim(0, 1.05)
        ax.tick_params(axis="x", labelsize=7, rotation=30)
        ax.set_ylabel("SANY Rate" if ax == axes[0] else "")
    fig.suptitle("SANY Pass Rate by Condition per Model")
    fig.tight_layout()
    p = out_dir / "per_condition_sany.png"
    fig.savefig(str(p), dpi=150)
    plt.close(fig)
    saved.append(p)

    # 3. per-tier sany heatmap
    if any("by_tier" in perf and perf["by_tier"] for perf in all_perf.values()):
        all_tiers = sorted({t for perf in all_perf.values() for t in perf.get("by_tier", {})})
        model_names = list(all_perf.keys())
        matrix = np.zeros((len(model_names), len(all_tiers)))
        for i, m in enumerate(model_names):
            for j, t in enumerate(all_tiers):
                bt = all_perf[m].get("by_tier", {}).get(t, {})
                matrix[i, j] = bt.get("sany_rate", 0.0)

        fig, ax = plt.subplots(figsize=(8, max(3, len(model_names))))
        im = ax.imshow(matrix, vmin=0, vmax=1, cmap="RdYlGn", aspect="auto")
        ax.set_xticks(range(len(all_tiers)))
        ax.set_xticklabels(all_tiers)
        ax.set_yticks(range(len(model_names)))
        ax.set_yticklabels(model_names)
        ax.set_title("SANY Pass Rate by Model × Complexity Tier")
        plt.colorbar(im, ax=ax, label="SANY Rate")
        for i in range(len(model_names)):
            for j in range(len(all_tiers)):
                ax.text(j, i, f"{matrix[i,j]:.2f}", ha="center", va="center", fontsize=9,
                        color="black" if 0.2 < matrix[i, j] < 0.8 else "white")
        fig.tight_layout()
        p = out_dir / "tier_heatmap.png"
        fig.savefig(str(p), dpi=150)
        plt.close(fig)
        saved.append(p)

    return saved


def run_analysis(use_wandb: bool = True) -> dict:
    all_perf: dict[str, dict] = {}

    for model in BASELINE_MODELS:
        records = load_run(model)
        if records:
            all_perf[model] = model_performance(records)
            logger.info("Loaded %d records for %s", len(records), model)
        else:
            logger.warning("No run file for %s", model)

    sp_records = load_spec_prover()
    if sp_records:
        all_perf["spec-prover"] = model_performance(sp_records)
        logger.info("Loaded %d spec-prover records", len(sp_records))

    if not all_perf:
        raise RuntimeError("No result files found. Run baselines first.")

    ranking = ranking_table(all_perf)
    hm_file = outputs_dir() / "results" / "hivemind.json"
    hivemind = load_json(hm_file) if hm_file.exists() else {}

    result = {
        "models_analyzed": list(all_perf.keys()),
        "per_model": all_perf,
        "ranking": ranking,
        "hivemind": hivemind.get("hivemind_index", {}),
        "aggregate_error_taxonomy": hivemind.get("aggregate_error_taxonomy", {}),
    }

    out_dir = outputs_dir() / "results"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "results_analysis.json"
    out_path.write_text(json.dumps(result, indent=2))
    logger.info("Saved results_analysis.json")

    fig_dir = out_dir / "results_figures"
    saved_figs = make_figures(all_perf, ranking, fig_dir)
    logger.info("Saved %d figures to %s", len(saved_figs), fig_dir)

    if use_wandb:
        try:
            import wandb
            run = wandb.init(project="tla_bench", name="results_analysis",
                             group="results_analysis", job_type="analysis")
            flat: dict = {}
            for model, perf in all_perf.items():
                ov = perf.get("overall", {})
                safe = model.replace("-", "_").replace(".", "_")
                for key in ("sany_rate", "tlc_rate", "pass1_rate",
                            "pass_at_1_unbiased", "pass_at_3_unbiased",
                            "pass_at_5_unbiased", "pass_at_10_unbiased"):
                    flat[f"results/{safe}/{key}"] = ov.get(key, 0.0)
                flat[f"results/{safe}/n"] = ov.get("n", 0)
            wandb.log(flat)
            for fig_path in saved_figs:
                wandb.log({f"figures/{fig_path.stem}": wandb.Image(str(fig_path))})
            rank_table = wandb.Table(
                columns=["model", "n", "sany_rate", "tlc_rate", "pass1_rate",
                         "pass_at_1_unbiased", "pass_at_3_unbiased", "pass_at_5_unbiased", "pass_at_10_unbiased"],
                data=[[r["model"], r["n"], r["sany_rate"], r["tlc_rate"], r["pass1_rate"],
                       r["pass_at_1_unbiased"], r["pass_at_3_unbiased"],
                       r["pass_at_5_unbiased"], r["pass_at_10_unbiased"]]
                      for r in ranking],
            )
            wandb.log({"results/ranking_table": rank_table})
            wandb.summary.update(flat)
            run.finish()
        except Exception as e:
            logger.warning("W&B logging failed: %s", e)

    logger.info("saved: %s", out_path)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description="TLA+Bench results analysis")
    parser.add_argument("--no-wandb", action="store_true")
    args = parser.parse_args()
    try:
        run_analysis(use_wandb=not args.no_wandb)
    except RuntimeError as e:
        logger.error("%s", e)
        sys.exit(1)


if __name__ == "__main__":
    main()
