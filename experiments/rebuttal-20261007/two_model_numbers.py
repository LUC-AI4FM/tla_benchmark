"""Every pooled number of the paper recomputed for the two commercial models that have new runs
(Claude Opus 4.5 and GPT-5), with the same rules as reproduce.py. Gemini-2.5-pro is left out
because Google's API no longer offers it to new users, so it could not be run again.

Run from the repository root:  python experiments/rebuttal-20261007/two_model_numbers.py
Writes experiments/rebuttal-20261007/two_model_numbers.json.
"""
import json, math
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "outputs"
MODELS = [("Claude Opus 4.5", "claude-opus-4-5"), ("GPT-5", "gpt-5")]
KEYS = {k for _, k in MODELS}
TIERS = ["basic", "intermediate", "advanced"]
CATEGORY = {"correct": "Correct", "config_bind_fail": "Config-binding", "no_cfg": "Config-binding",
            "parse_fail": "Parse failure", "semantic_fail": "Malformed temporal",
            "safety_violation": "Safety violation", "liveness_violation": "Liveness violation",
            "runtime_error": "Run-time error", "deadlock": "Deadlock", "resource_limit": "Resource limit"}


def load(*p):
    return json.loads(OUT.joinpath(*p).read_text())


def by_id(rows):
    return {str(r["spec_id"]): r for r in rows}


ids = [str(s) for s in load("eval_100_ids.json")]
no_cfg = {g["spec_id"] for g in load("audit", "gold_without_cfg.json") if g["in_eval"]}
single = {r["spec_id"] for r in load("audit", "fixture_audit.json") if r.get("distinct") == 1}
clean = [s for s in ids if s not in no_cfg and s not in single]
res = {k: by_id(load(f"{k}.json")) for _, k in MODELS}
cfg = {k: by_id(load("cfgaware", f"{k}.json")) for _, k in MODELS}
man = {str(json.loads(l)["spec_id"]): json.loads(l) for l in open(ROOT / "manifest.jsonl")}
n_out = len(ids) * len(MODELS)
out = {"models": [m for m, _ in MODELS], "outputs": n_out}

# Table 6 and Table A7
out["table6"] = {m: {"parse": sum(bool(res[k][s].get("sany_pass")) for s in ids),
                     "correct": sum(res[k][s]["label"] == "correct" for s in ids)} for m, k in MODELS}
out["tableA7_cfgaware"] = {m: sum(bool(cfg[k][s].get("tlc_pass")) for s in ids) for m, k in MODELS}

# Table A4 failure categories
out["tableA4"] = {m: dict(Counter(CATEGORY.get(res[k][s]["label"], "Other") for s in ids)) for m, k in MODELS}

# Table A6 by difficulty tier
tier_ids = {t: [s for s in ids if man[s].get("complexity") == t] for t in TIERS}
a6 = {}
for m, k in MODELS + [("Pooled", None)]:
    a6[m] = {}
    for t in TIERS:
        ks = [kk for _, kk in MODELS] if k is None else [k]
        n = len(tier_ids[t]) * len(ks)
        p = sum(bool(res[kk][s].get("sany_pass")) for kk in ks for s in tier_ids[t])
        c = sum(bool(res[kk][s].get("tlc_pass")) for kk in ks for s in tier_ids[t])
        a6[m][t] = {"n": n, "parse_pct": round(100 * p / n, 1), "correct_pct": round(100 * c / n, 1)}
out["tableA6"] = a6

# Pass-quality analyses on the default passes of these two models
keep = lambda rows: [r for r in rows if r["model"] in KEYS and r["spec_id"] in set(ids)]
mut = keep(load("pass_quality", "mutation_default.json"))
ref = keep(load("pass_quality", "refcheck_default.json"))
audit12 = keep(load("pass_quality", "audit12.json"))
audit = keep(load("_pass_audit.json"))
passes = sum(res[k][s]["label"] == "correct" for _, k in MODELS for s in ids)
assert len(mut) == len(ref) == len(audit) == passes, (len(mut), len(ref), len(audit), passes)
decided = {(r["model"], r["spec_id"]): r["behavior"] for r in ref
           if r.get("behavior") in ("same_behaviors", "omits_reference_behavior")}
decided.update({(r["model"], r["spec_id"]): r["behavior"] for r in audit12})
behavior = Counter(decided.get((r["model"], r["spec_id"]), "undecided") for r in ref)
same_on_single = sum(1 for r in ref if decided.get((r["model"], r["spec_id"])) == "same_behaviors"
                     and r["spec_id"] in single)
out["correct_outputs"] = passes
out["reference_comparison"] = dict(behavior)
out["reference_comparison_same_on_single_state"] = same_on_single
out["reference_comparison_resolved_by_hand"] = len(audit12)
out["reference_properties"] = dict(Counter(r["ref_props"] for r in ref))
out["mutation"] = dict(Counter(r["verdict"] for r in mut))
out["checks_named"] = dict(Counter("invariant" if r["checks"]["INVARIANT"] else
                                   "temporal property" if r["checks"]["PROPERTY"] else "nothing named"
                                   for r in mut))

# Table 5 envelope over the two models
out["table5"] = {
    "configuration_aware": sum(out["tableA7_cfgaware"].values()),
    "default": passes,
    "same_behaviors_as_reference": behavior["same_behaviors"],
    "substantive": sum(1 for r in audit if not r["degenerate"] and r["real_props"] > 0),
    "mutation": out["mutation"].get("load_bearing", 0),
    "denominator": n_out,
}

# Without the item lacking a configuration and the six single-state references
out["clean_set"] = {"items": len(clean),
                    **{m: {"correct_pct": round(100 * sum(res[k][s]["label"] == "correct" for s in clean) / len(clean), 1),
                           "parse_pct": round(100 * sum(bool(res[k][s].get("sany_pass")) for s in clean) / len(clean), 1)}
                       for m, k in MODELS}}

# Paired test between the two models
a, b = (res[k] for _, k in MODELS)
only_a = sum(a[s]["label"] == "correct" and b[s]["label"] != "correct" for s in ids)
only_b = sum(b[s]["label"] == "correct" and a[s]["label"] != "correct" for s in ids)
n = only_a + only_b
out["mcnemar_opus_vs_gpt5"] = {"only_opus": only_a, "only_gpt5": only_b,
                              "exact_p": min(1.0, 2 * sum(math.comb(n, i) for i in range(min(only_a, only_b) + 1)) / 2 ** n)}

(ROOT / "experiments/rebuttal-20261007/two_model_numbers.json").write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
