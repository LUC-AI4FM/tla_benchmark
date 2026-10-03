#!/usr/bin/env python3
"""Recompute every reported number of TLA+-Bench from the released files.

Every figure printed here is counted from a file under outputs/. Nothing is typed in:
there are no result constants in this script, and every denominator is the number of
graded outputs actually read. The script does not query any model.

Tables follow the numbering of the compiled paper:
  Table 6   parse and correct rate per model, default regime          (tab:main)
  Table A7  default vs configuration-aware correct rate              (tab:twomodes)
  Table A4  failure categories per frontier model                    (tab:failures)
  Table A6  parse and correct rate by difficulty tier                (tab:difficulty-results)
  Table 5   the correctness envelope, pooled over the frontier models (tab:envelope)
  Sec. 8.7  pass quality: behavior-mutation test and reference check

All tables are computed on the 100 evaluation specifications of the paper
(outputs/eval_100_ids.json). With --clean, the script also prints every table on the
subset that excludes the specification without a configuration and the references with a
single reachable state (outputs/audit/).

The previous version of this script is kept as reproduce_as_submitted.py. It printed the
configuration-aware and mutation rows from typed-in values; see CHANGES in README.md.

Usage:
    python reproduce.py            # the 100 evaluation specifications
    python reproduce.py --clean    # also the subset described above
"""
import argparse
import json
import os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "outputs")

FRONTIER = [("Claude Opus 4.5", "claude-opus-4-5"), ("Gemini-2.5-pro", "gemini-2-5-pro"), ("GPT-5", "gpt-5")]
OPEN = [("qwen2.5-coder-32b", "qwen2.5-coder-32b"), ("llama3.3-70b", "llama3.3-70b"), ("gpt-oss-20b", "gpt-oss-20b")]
# failure labels written by the grader -> categories of Table 4. A missing configuration
# counts as a configuration-binding failure (Section 7).
CATEGORY = {"correct": "Correct", "config_bind_fail": "Config-binding", "no_cfg": "Config-binding",
            "parse_fail": "Parse failure", "semantic_fail": "Malformed temporal",
            "safety_violation": "Safety violation", "liveness_violation": "Liveness violation",
            "runtime_error": "Run-time error", "deadlock": "Deadlock", "resource_limit": "Resource limit"}
TIERS = ["basic", "intermediate", "advanced"]


def load(*parts):
    with open(os.path.join(OUT, *parts), encoding="utf-8") as f:
        return json.load(f)


def by_id(rows):
    return {str(r["spec_id"]): r for r in rows}


def pct(k, n):
    return f"{k}/{n} = {100 * k / n:5.1f}%" if n else "n/a"


def evaluation_sets(with_clean):
    paper = [str(s) for s in load("eval_100_ids.json")]
    no_cfg = {g["spec_id"] for g in load("audit", "gold_without_cfg.json") if g["in_eval"]}
    single = {r["spec_id"] for r in load("audit", "fixture_audit.json") if r.get("distinct") == 1}
    sets = {"paper": paper}
    if with_clean:
        sets["clean"] = [s for s in paper if s not in no_cfg and s not in single]
    return sets, sorted(no_cfg, key=int), sorted(single, key=int)


def default_results():
    res = {key: by_id(load(f"{key}.json")) for _, key in FRONTIER}
    for _, key in OPEN:
        res[key] = by_id(load("contamination", f"{key}__clean.json"))
    return res


def cfgaware_results():
    """Frontier models always; an open model only if its config-aware results are released."""
    return {key: by_id(load("cfgaware", f"{key}.json")) for _, key in FRONTIER + OPEN
            if os.path.exists(os.path.join(OUT, "cfgaware", f"{key}.json"))}


def table6(sets, res):
    print("Table 6: parse and correct rate, default regime")
    for name, ids in sets.items():
        print(f"  [{name}, {len(ids)} specs]")
        for label, key in FRONTIER + OPEN:
            rows = [res[key][s] for s in ids]
            print(f"    {label:18s} parse {pct(sum(bool(r.get('sany_pass')) for r in rows), len(rows)):>18s}"
                  f"   correct {pct(sum(bool(r.get('tlc_pass')) for r in rows), len(rows)):>18s}")
    print()


def tableA7(sets, res, cfg):
    print("Table A7: default vs configuration-aware correct rate")
    for name, ids in sets.items():
        print(f"  [{name}, {len(ids)} specs]")
        for label, key in FRONTIER:
            d = sum(bool(res[key][s].get("tlc_pass")) for s in ids)
            c = sum(bool(cfg[key][s].get("tlc_pass")) for s in ids)
            print(f"    {label:18s} default {pct(d, len(ids)):>18s}   config-aware {pct(c, len(ids)):>18s}")
        for label, key in OPEN:
            d = sum(bool(res[key][s].get("tlc_pass")) for s in ids)
            if key in cfg:
                c = sum(bool(cfg[key][s].get("tlc_pass")) for s in ids)
                print(f"    {label:18s} default {pct(d, len(ids)):>18s}   config-aware {pct(c, len(ids)):>18s}")
            else:
                print(f"    {label:18s} default {pct(d, len(ids)):>18s}   config-aware  not run")
    print()


def tableA4(sets, res):
    print("Table A4: failure categories per frontier model (counts)")
    cats = list(dict.fromkeys(CATEGORY.values()))
    for name, ids in sets.items():
        counts = {key: Counter(CATEGORY.get(res[key][s].get("label"), "Other") for s in ids)
                  for _, key in FRONTIER}
        print(f"  [{name}, {len(ids)} specs]  " + "  ".join(f"{label:>15s}" for label, _ in FRONTIER))
        for c in cats + (["Other"] if any(counts[k]["Other"] for k in counts) else []):
            print(f"    {c:20s}" + "  ".join(f"{counts[key][c]:15d}" for _, key in FRONTIER))
    print()


def tableA6(sets, res):
    print("Table A6: parse (P) and correct (C) by difficulty tier, frontier models")
    man = {str(json.loads(l)["spec_id"]): json.loads(l) for l in open(os.path.join(HERE, "manifest.jsonl"))}
    for name, ids in sets.items():
        tier_ids = {t: [s for s in ids if man[s].get("complexity") == t] for t in TIERS}
        print(f"  [{name}]  " + "  ".join(f"{t} (n={len(tier_ids[t])})".rjust(26) for t in TIERS))
        pooled = {t: [0, 0, 0] for t in TIERS}
        for label, key in FRONTIER:
            cells = []
            for t in TIERS:
                p = sum(bool(res[key][s].get("sany_pass")) for s in tier_ids[t])
                c = sum(bool(res[key][s].get("tlc_pass")) for s in tier_ids[t])
                n = len(tier_ids[t])
                pooled[t][0] += p; pooled[t][1] += c; pooled[t][2] += n
                cells.append(f"P {100 * p / n:5.1f}%  C {100 * c / n:5.1f}%" if n else "n/a")
            print(f"    {label:18s}" + "  ".join(x.rjust(26) for x in cells))
        print(f"    {'Pooled':18s}" + "  ".join(
            f"P {100 * p / n:5.1f}%  C {100 * c / n:5.1f}%".rjust(26) for p, c, n in pooled.values()))
    print()


def pass_quality_rows(ids):
    keep = set(ids)
    global audit12
    audit12 = [r for r in load("pass_quality", "audit12.json") if r["spec_id"] in keep]
    mut = [r for r in load("pass_quality", "mutation_default.json") if r["spec_id"] in keep]
    ref = [r for r in load("pass_quality", "refcheck_default.json") if r["spec_id"] in keep]
    audit = [r for r in load("_pass_audit.json") if r["spec_id"] in keep]
    return mut, ref, audit


def table5(sets, res, cfg):
    print("Table 5: correctness envelope, pooled over the three frontier models")
    for name, ids in sets.items():
        n = len(ids) * len(FRONTIER)
        mut, ref, audit = pass_quality_rows(ids)
        rows = [
            ("Configuration-aware", "interface names supplied",
             sum(bool(cfg[key][s].get("tlc_pass")) for _, key in FRONTIER for s in ids)),
            ("Default", "interface must be recovered",
             sum(bool(res[key][s].get("tlc_pass")) for _, key in FRONTIER for s in ids)),
            ("Substantive", "pass moves and checks a behavioral property",
             sum(1 for r in audit if not r["degenerate"] and r["real_props"] > 0)),
            ("Behavior-mutation", "a named property catches a behavior change",
             sum(1 for r in mut if r["verdict"] == "load_bearing")),
            ("Matches reference", "same behaviors as the reference (TLC, both directions)",
             sum(1 for r in ref if r.get("behavior") == "same_behaviors")
             + sum(1 for r in audit12 if r["behavior"] == "same_behaviors")),
        ]
        print(f"  [{name}, {n} outputs]")
        for regime, asks, k in rows:
            print(f"    {regime:20s} {asks:52s} {pct(k, n):>18s}")
    print()


def section87(sets):
    print("Section 8.7: pass quality of the default-regime passes")
    ref_mut = by_id(load("pass_quality", "mutation_reference.json"))
    for name, ids in sets.items():
        mut, ref, _ = pass_quality_rows(ids)
        checks = Counter("invariant" if r["checks"]["INVARIANT"] else
                         "temporal property" if r["checks"]["PROPERTY"] else "nothing named"
                         for r in mut)
        print(f"  [{name}] {len(mut)} passing outputs")
        print(f"    configuration checks : {dict(checks)}")
        print(f"    behavior-mutation    : {dict(Counter(r['verdict'] for r in mut))}")
        print(f"    reference properties : {dict(Counter(r['ref_props'] for r in ref))}")
        print(f"    behavior vs reference (identity mapping): "
              f"{dict(Counter(r.get('behavior') or 'cfg_names_no_SPECIFICATION' for r in ref))}")
        print(f"    audit of the undecided cases (explicit mappings): "
              f"{dict(Counter(r['behavior'] for r in audit12))}")
        decided = {(r['model'], r['spec_id']): r['behavior'] for r in ref
                   if r.get('behavior') in ('same_behaviors', 'omits_reference_behavior')}
        decided.update({(r['model'], r['spec_id']): r['behavior'] for r in audit12})
        print(f"    combined over the {len(ref)} passes: "
              f"{dict(Counter(decided.get((r['model'], r['spec_id']), 'different_algorithm') for r in ref))}")
        same = sum(1 for r in mut if r["verdict"] == ref_mut.get(r["spec_id"], {}).get("verdict"))
        print(f"    same mutation verdict as the pass's own reference: {same} of {len(mut)}")
    for name, ids in sets.items():
        refs = [ref_mut[s] for s in ids if s in ref_mut]
        print(f"  [{name}] references tested: {len(refs)} of {len(ids)} (a reference without a "
              f"configuration cannot be run); verdicts {dict(Counter(r['verdict'] for r in refs))}")
    ctl = load("pass_quality", "mutation_control.json")
    print("  control (real property vs. V == x = x): " + ", ".join(
        f"{r['model']} {r['spec_id']} -> {r['verdict']}" for r in ctl))
    print()


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--clean", action="store_true", help="also report the subset described in the docstring")
    args = ap.parse_args()
    sets, no_cfg, single = evaluation_sets(args.clean)
    print(f"Evaluation set: {len(sets['paper'])} specifications (outputs/eval_100_ids.json).")
    print(f"Audit: no configuration {no_cfg}; single reachable state {single} (outputs/audit/).")
    if args.clean:
        print(f"--clean: also reporting the {len(sets['clean'])} specifications without these.")
    print()
    res, cfg = default_results(), cfgaware_results()
    table6(sets, res)
    tableA7(sets, res, cfg)
    tableA4(sets, res)
    tableA6(sets, res)
    table5(sets, res, cfg)
    section87(sets)
    print("Every number above was counted from files under outputs/.")
    print("To re-grade a generated specification from source, run code/validator.py.")
