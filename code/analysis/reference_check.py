#!/usr/bin/env python3
"""Rebuttal item 5: an independent semantic check of passing outputs against the reference.

The benchmark's oracle checks the properties named in the cfg as the GENERATED module
defines them, so a model can pass with a weaker property or with missing behavior
(reviewers ST87, d77E). Two checks use the reference module instead:

A. Reference properties. The cfg's INVARIANT / PROPERTY operators are copied from the
   reference module (with every reference definition they depend on), renamed REF_*, added
   to the generated module, and checked on the generated specification.

B. Behavior comparison, when the cfg names a SPECIFICATION S.
   forward : the reference's S (copied as REF_S) is checked as a temporal property of the
             generated specification. Fails when the generated spec has behavior the
             reference does not allow.
   reverse : the generated module's S (copied as GEN_S into the reference module) is checked
             as a property of the reference specification. Fails when the reference has
             behavior the generated spec does not allow, i.e. the generated spec omits it.
   Both hold: the two specifications allow the same behaviors on the shared variables.

A check is "not applicable" when the copied definitions mention variables or constants the
other module does not declare, so they cannot be evaluated there.

Usage:
    python code/analysis/refcheck.py --regime default
    python code/analysis/refcheck.py --regime cfgaware
"""
from __future__ import annotations
import argparse, json, re, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tla_lib as R
from mutation_test import passing_outputs

ROOT = R.ROOT


def import_defs(target: str, source: str, roots: list[str], prefix: str) -> tuple[str, dict]:
    """Copy roots and their dependencies from source into target, renamed with prefix."""
    sdefs = R.definitions(source)
    names = R.closure(sdefs, roots)
    block = "\n\n".join(R.rename(sdefs[n]["text"], set(names), prefix) for n in names)
    out = R.add_extends(target, R.extends_of(source))
    return R.append_defs(out, f"\\* ---- copied for the rebuttal check ({prefix}*) ----\n" + block), \
        {n: prefix + n for n in names}


def rewrite_cfg(cfg_text: str, keep_checks: bool, extra: dict[str, list[str]],
                mapping: dict[str, str] | None = None) -> str:
    """Rebuild a cfg: drop or rename INVARIANT/PROPERTY entries, append extra sections."""
    c = R.parse_cfg(cfg_text)
    lines = []
    for k, vals in c.items():
        if k in ("INVARIANT", "PROPERTY"):
            if not keep_checks:
                continue
            vals = [(mapping or {}).get(v, v) for v in vals]
        if k == "CONSTANT":
            lines.append("CONSTANTS")
            lines += [f"  {v}" for v in vals]
        elif vals:
            lines.append(f"{k} " + " ".join(vals))
        else:
            lines.append(k)
    for k, vals in extra.items():
        lines.append(f"{k} " + " ".join(vals))
    return "\n".join(lines) + "\n"


def verdict(res: dict, behavior: bool = False) -> str:
    """behavior=True for the refinement checks: a value-encoding mismatch (e.g. BOOLEAN where
    the other module uses 0..1) means the identity mapping cannot compare the two modules,
    not that their behaviors differ; audit_undecided.py compares them under a mapping."""
    st = res["status"]
    if st == "pass":
        return "holds"
    if behavior and st == "value_mismatch":
        return "not_applicable"
    if st in ("invariant_violated", "property_violated", "value_mismatch"):
        return "violated"
    if st == "parse_error":
        return "not_applicable"
    if st == "deadlock":
        return "deadlock"
    return st


def evaluate(job: dict) -> dict:
    tla, cfg = R.O.gold_paths(job["spec_id"])
    ref = tla.read_text(errors="replace")
    gen = job["gen"].read_text(errors="replace")
    cfg_text = cfg.read_text(errors="replace")
    c = R.parse_cfg(cfg_text)
    named = c.get("INVARIANT", []) + c.get("PROPERTY", [])
    rec = {"model": job["model"], "spec_id": job["spec_id"], "checks": named}

    # A. reference properties
    if not named:
        rec["ref_props"] = "no_named_property"
    else:
        rdefs = R.definitions(ref)
        missing = [n for n in named if n not in rdefs]
        if missing:
            rec["ref_props"] = "not_applicable"
            rec["ref_props_note"] = f"reference does not define {missing}"
        else:
            g2, mp = import_defs(gen, ref, named, "REF_")
            res = R.run_tlc_on(g2, tla, rewrite_cfg(cfg_text, True, {}, mp), timeout=120)
            rec["ref_props"], rec["ref_props_tlc"] = verdict(res), res
        gdefs = R.definitions(gen)
        same = [n for n in named if n in gdefs and n in rdefs and
                re.sub(r"\s+", " ", R.strip_tla_comments(gdefs[n]["text"])).strip() ==
                re.sub(r"\s+", " ", R.strip_tla_comments(rdefs[n]["text"])).strip()]
        rec["identical_property_defs"] = same

    # B. behavior comparison
    spec = c.get("SPECIFICATION", [])
    if not spec:
        rec["forward"] = rec["reverse"] = "no_specification_in_cfg"
    else:
        s = spec[0]
        base = rewrite_cfg(cfg_text, False, {})
        if s not in R.definitions(ref):
            rec["forward"] = "not_applicable"
        else:
            g2, mp = import_defs(gen, ref, [s], "REF_")
            res = R.run_tlc_on(g2, tla, base + f"PROPERTY {mp[s]}\n", timeout=180)
            rec["forward"], rec["forward_tlc"] = verdict(res, behavior=True), res
        if s not in R.definitions(gen):
            rec["reverse"] = "not_applicable"
        else:
            r2, mp = import_defs(ref, gen, [s], "GEN_")
            res = R.run_tlc_on(r2, tla, base + f"PROPERTY {mp[s]}\n", timeout=180)
            rec["reverse"], rec["reverse_tlc"] = verdict(res, behavior=True), res
        f, r = rec["forward"], rec["reverse"]
        rec["behavior"] = ("same_behaviors" if f == r == "holds" else
                           "omits_reference_behavior" if f == "holds" and r == "violated" else
                           "adds_behavior" if f == "violated" and r == "holds" else
                           "differs_both_ways" if f == r == "violated" else
                           "not_applicable")
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--regime", choices=["default", "cfgaware"], default="default")
    ap.add_argument("--workers", type=int, default=6)
    a = ap.parse_args()

    jobs = passing_outputs(a.regime)
    with ThreadPoolExecutor(a.workers) as ex:
        recs = sorted(ex.map(evaluate, jobs), key=lambda r: (r["model"], int(r["spec_id"])))
    dest = ROOT / "outputs/rerun"; dest.mkdir(parents=True, exist_ok=True)
    json.dump(recs, open(dest / f"refcheck_{a.regime}.json", "w"), indent=2)

    print(f"regime={a.regime}: {len(recs)} passing outputs")
    for r in recs:
        print(f"  {r['model']:16s} {r['spec_id']:5s} ref_props={r['ref_props']:17s} "
              f"fwd={r.get('forward')!s:15s} rev={r.get('reverse')!s:15s} -> {r.get('behavior')}")
    print("reference properties:", dict(Counter(r["ref_props"] for r in recs)))
    print("behavior comparison:", dict(Counter(r.get("behavior") for r in recs)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
