#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from utils import data_dir, get_logger, load_json, outputs_dir, repo_root, save_json

logger = get_logger("analyze_dataset")

TIER_ORDER = ["basic", "intermediate", "advanced"]

BOOL_FEATURES = [
    "Implication", "Negation", "BooleanConstants", "Quantifiers", "EqualityOps",
    "MembershipOps", "IfThenElse", "CaseExpr", "SetEnumeration", "SetOperators",
    "FiniteSetOps", "FunctionConstructor", "FunctionApplication", "FunctionOverride",
    "RecordConstructor", "RecordAccess", "TupleConstructor", "SequenceOps",
    "ArithmeticOps", "ComparisonOps", "RangeExpr", "ChoiceExpr", "StringLiterals",
    "ArithmeticModules", "DataStructureModules", "ToolingModules",
    "PrimedVariables", "UnchangedExprs", "EnabledExprs", "TemporalSubscript",
    "AlwaysOp", "EventuallyOp", "LeadsToOp", "GuaranteesOp", "ActionComposition",
    "FairnessConditions", "ProofHints", "ProofCommands", "ProofStructureSteps",
    "AssumeProveBlocks", "PlusCalAlgorithm", "PlusCalProcesses", "ModelValues",
    "OperatorOverrides", "SymmetrySet", "StateConstraint", "ActionConstraint",
    "ViewExpr",
]

LIST_FEATURES = [
    "ConstantNames", "VariableNames", "OperatorDefNames", "ActionDefNames",
    "TheoremNames", "ExtendsModules", "InstanceModules",
]


def load_records() -> list[dict]:
    index = load_json(data_dir() / "index.json")
    records = []
    for entry in index.values():
        parsed_path = repo_root() / entry["parsed_path"]
        try:
            v3 = load_json(parsed_path)
            v3["spec_id"] = entry["spec_id"]
            v3["complexity_tier"] = entry["complexity_tier"]
            records.append(v3)
        except Exception as exc:
            logger.warning("skip spec=%d: %s", entry["spec_id"], exc)
    return records


def tier_distribution(records: list) -> dict:
    counts = Counter(r.get("complexity_tier", "") for r in records)
    total = len(records)
    return {
        t: {"count": counts.get(t, 0), "pct": round(100 * counts.get(t, 0) / total, 1)}
        for t in TIER_ORDER if counts.get(t, 0) > 0
    }


def feature_prevalence(records: list) -> dict:
    total = len(records)
    result = {}
    for feat in BOOL_FEATURES:
        count = sum(1 for r in records if r.get(feat))
        result[feat] = {"count": count, "pct": round(100 * count / total, 1)}
    return dict(sorted(result.items(), key=lambda x: -x[1]["count"]))


def list_feature_stats(records: list) -> dict:
    stats = {}
    for feat in LIST_FEATURES:
        lengths = [len(r.get(feat, [])) for r in records]
        stats[feat] = {
            "mean":   round(float(np.mean(lengths)), 2),
            "median": float(np.median(lengths)),
            "max":    int(np.max(lengths)),
            "min":    int(np.min(lengths)),
            "std":    round(float(np.std(lengths)), 2),
        }
    return stats


def split_stats(records: list) -> dict:
    split = load_json(data_dir() / "test_split.json")
    train_ids = set(split.get("train_ids", []))
    test_ids  = set(split.get("test_ids", []))

    id_to_tier = {r["spec_id"]: r.get("complexity_tier", "") for r in records}

    def tier_counts(ids):
        c = Counter(id_to_tier.get(i, "") for i in ids)
        return {t: c.get(t, 0) for t in TIER_ORDER if c.get(t, 0) > 0}

    return {
        "train": {"n": len(train_ids), "tiers": tier_counts(train_ids)},
        "test":  {"n": len(test_ids),  "tiers": tier_counts(test_ids)},
    }


def operator_complexity_profile(records: list) -> dict:
    temporal_ops = ["AlwaysOp", "EventuallyOp", "LeadsToOp", "GuaranteesOp", "FairnessConditions", "TemporalSubscript"]
    pluscal = ["PlusCalAlgorithm", "PlusCalProcesses"]

    profiles = {}
    for tier in TIER_ORDER:
        tier_recs = [r for r in records if r.get("complexity_tier", "") == tier]
        if not tier_recs:
            continue
        n = len(tier_recs)
        profiles[tier] = {
            "n": n,
            "pct_temporal": round(100 * sum(1 for r in tier_recs if any(r.get(op) for op in temporal_ops)) / n, 1),
            "pct_pluscal":  round(100 * sum(1 for r in tier_recs if any(r.get(op) for op in pluscal)) / n, 1),
            "pct_proof":    round(100 * sum(1 for r in tier_recs if r.get("ProofHints") or r.get("ProofCommands")) / n, 1),
            "pct_choice":   round(100 * sum(1 for r in tier_recs if r.get("ChoiceExpr")) / n, 1),
            "avg_variables": round(float(np.mean([len(r.get("VariableNames", [])) for r in tier_recs])), 2),
            "avg_operators": round(float(np.mean([len(r.get("OperatorDefNames", [])) for r in tier_recs])), 2),
        }
    return profiles


def rare_features(records: list, threshold_pct: float = 5.0) -> list:
    total = len(records)
    rare = []
    for feat in BOOL_FEATURES:
        count = sum(1 for r in records if r.get(feat))
        pct = 100 * count / total
        if pct <= threshold_pct:
            rare.append({"feature": feat, "count": count, "pct": round(pct, 1)})
    return sorted(rare, key=lambda x: x["count"])


def corpus_distribution(records: list) -> dict:
    sources = Counter()
    for r in records:
        parsed_path = r.get("CorpusSource", "")
        parts = parsed_path.split("/")
        org = parts[0] if parts else "unknown"
        sources[org] += 1
    return dict(sources.most_common())


def make_figures(stats: dict, out_dir: Path) -> list[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    saved = []

    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        logger.warning("matplotlib not available, skipping figures")
        return []

    tier_data = stats["tier_distribution"]
    tiers = list(tier_data.keys())
    counts = [tier_data[t]["count"] for t in tiers]
    fig, ax = plt.subplots(figsize=(7, 4))
    bars = ax.bar(tiers, counts, color=["#4C72B0", "#DD8452", "#55A868"])
    ax.set_xlabel("complexity tier")
    ax.set_ylabel("number of specs")
    ax.set_title("tla+bench: spec distribution by complexity tier")
    for bar, count in zip(bars, counts):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.5,
                str(count), ha="center", va="bottom", fontsize=11)
    fig.tight_layout()
    p = out_dir / "tier_distribution.png"
    fig.savefig(str(p), dpi=150)
    plt.close(fig)
    saved.append(p)

    feat_data = stats["feature_prevalence"]
    feats = list(feat_data.keys())[:20]
    pcts = [feat_data[f]["pct"] for f in feats]
    fig, ax = plt.subplots(figsize=(9, 7))
    ax.barh(feats[::-1], pcts[::-1], color="#4C72B0")
    ax.set_xlabel("% of specs")
    ax.set_title("feature prevalence (top 20 tla+ constructs)")
    ax.set_xlim(0, 105)
    for i, (feat, pct) in enumerate(zip(feats[::-1], pcts[::-1])):
        ax.text(pct + 1, i, f"{pct}%", va="center", fontsize=8)
    fig.tight_layout()
    p = out_dir / "feature_prevalence.png"
    fig.savefig(str(p), dpi=150)
    plt.close(fig)
    saved.append(p)

    op_profile = stats["operator_complexity_by_tier"]
    if op_profile:
        tier_names = list(op_profile.keys())
        metrics = ["pct_temporal", "pct_pluscal", "pct_proof"]
        labels = ["temporal ops", "pluscal", "proofs"]
        x = np.arange(len(tier_names))
        w = 0.25
        fig, ax = plt.subplots(figsize=(9, 5))
        for i, (m, lbl) in enumerate(zip(metrics, labels)):
            ax.bar(x + i * w, [op_profile[t][m] for t in tier_names], w, label=lbl)
        ax.set_xticks(x + w)
        ax.set_xticklabels(tier_names)
        ax.set_ylabel("% of tier specs")
        ax.set_title("operator profiles by complexity tier")
        ax.legend()
        fig.tight_layout()
        p = out_dir / "operator_complexity_by_tier.png"
        fig.savefig(str(p), dpi=150)
        plt.close(fig)
        saved.append(p)

    records_ref = stats.get("_records_ref")
    if records_ref is not None:
        var_counts = [len(r.get("VariableNames", [])) for r in records_ref]
        fig, ax = plt.subplots(figsize=(7, 4))
        ax.hist(var_counts, bins=range(0, min(max(var_counts) + 2, 30)), color="#55A868", edgecolor="white")
        ax.set_xlabel("number of variables")
        ax.set_ylabel("number of specs")
        ax.set_title("distribution of variable count per spec")
        fig.tight_layout()
        p = out_dir / "variable_count_distribution.png"
        fig.savefig(str(p), dpi=150)
        plt.close(fig)
        saved.append(p)

    return saved


def run_analysis(use_wandb: bool = True) -> dict:
    index_file = data_dir() / "index.json"
    if not index_file.exists():
        raise RuntimeError("index.json not found, run scripts/build_dataset.py first")

    records = load_records()
    logger.info("loaded %d records for dataset analysis", len(records))

    stats = {
        "_records_ref": records,
        "total_specs":               len(records),
        "tier_distribution":         tier_distribution(records),
        "feature_prevalence":        feature_prevalence(records),
        "list_feature_stats":        list_feature_stats(records),
        "split_stats":               split_stats(records),
        "operator_complexity_by_tier": operator_complexity_profile(records),
        "rare_features_le5pct":      rare_features(records, threshold_pct=5.0),
        "corpus_distribution":       corpus_distribution(records),
    }

    out_dir = outputs_dir() / "results"
    out_dir.mkdir(parents=True, exist_ok=True)
    save_stats = {k: v for k, v in stats.items() if not k.startswith("_")}
    save_json(save_stats, out_dir / "dataset_stats.json")
    logger.info("saved dataset_stats.json")

    saved_figs = make_figures(stats, out_dir / "dataset_figures")
    logger.info("saved %d figures", len(saved_figs))

    if use_wandb:
        try:
            import wandb
            run = wandb.init(project="tla_bench", name="dataset_analysis",
                             group="dataset_analysis", job_type="analysis")
            flat: dict = {}
            for t, v in stats["tier_distribution"].items():
                flat[f"dataset/tier/{t}_count"] = v["count"]
                flat[f"dataset/tier/{t}_pct"]   = v["pct"]
            sp = stats["split_stats"]
            flat.update({"dataset/train_n": sp["train"]["n"], "dataset/test_n": sp["test"]["n"],
                         "dataset/total_specs": stats["total_specs"]})
            for tier, profile in stats["operator_complexity_by_tier"].items():
                for metric in ["pct_temporal", "pct_pluscal", "pct_proof", "avg_variables", "avg_operators"]:
                    flat[f"dataset/tier_profile/{tier}/{metric}"] = profile[metric]
            wandb.log(flat)
            for fig_path in saved_figs:
                wandb.log({f"figures/{fig_path.stem}": wandb.Image(str(fig_path))})
            wandb.summary.update(flat)
            run.finish()
        except Exception as exc:
            logger.warning("wandb logging failed: %s", exc)

    return stats


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-wandb", action="store_true")
    args = parser.parse_args()
    run_analysis(use_wandb=not args.no_wandb)


if __name__ == "__main__":
    main()
