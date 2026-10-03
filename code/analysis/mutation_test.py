#!/usr/bin/env python3
r"""Rebuttal item 4: behavior-mutation test for passing outputs.

The July test replaced the checked invariant with TRUE, which can only make a run pass
more easily, so it could not show whether a property does work (reviewers d77E, ST87).
This test mutates the specification's BEHAVIOR instead and asks whether the checked
properties notice.

For each passing output:
  - every action definition (a top-level definition whose body has a primed variable or
    UNCHANGED) is scanned for guard conjuncts: bullet items  /\ g  with no primed variable
  - two mutants per guard: the guard deleted (replaced by TRUE) and, for a one-line guard,
    the guard negated
  - each mutant is model-checked with the ORIGINAL configuration

Mutant outcomes:
  killed_property   TLC reports a violated invariant or temporal property named in the cfg
  killed_deadlock   TLC reports a deadlock (default deadlock checking)
  survived_changed  TLC passes and the distinct-state count changed, so behavior changed
                    and no check noticed
  survived_same     TLC passes with the same distinct-state count (possibly equivalent)
  invalid           parse error, evaluation error, or timeout

Pass verdicts:
  load_bearing      at least one mutant killed by a named property
  deadlock_only     no property kill, at least one deadlock kill
  not_load_bearing  behavior-changing mutants exist and none was killed
  no_named_property the cfg names no invariant or property (nothing to be load-bearing)
  inconclusive      no mutant changed behavior

Usage:
    python code/analysis/mutation.py --regime default
    python code/analysis/mutation.py --regime cfgaware
"""
from __future__ import annotations
import argparse, json, re, sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tla_lib as R

ROOT = R.ROOT
PRIMED = re.compile(r"[\w)\]}]'")
MAX_MUTANTS = 40
# single-state tool regression fixtures found in the evaluation set (fixture_audit.json)
FIXTURES = {"1275", "1343", "1413", "1435", "1455", "1504"}
# passes whose named property the default-regime test found load-bearing; used as controls
CONTROLS = [("claude-opus-4-5", "891"), ("claude-opus-4-5", "1279"), ("gemini-2-5-pro", "930")]


def vacuous_control(job: dict) -> dict:
    """Same generated module, but the cfg checks a new invariant  V == x = x  instead of the
    real one. The test must call this not load-bearing."""
    tla, cfg = R.O.gold_paths(job["spec_id"])
    gen = job["gen"].read_text(errors="replace")
    var = re.search(r"^VARIABLES?\s+([A-Za-z_]\w*)", gen, flags=re.M).group(1)
    text = R.append_defs(gen, f"VacuousControl == {var} = {var}")
    c = R.parse_cfg(cfg.read_text(errors="replace"))
    c["INVARIANT"] = ["VacuousControl"]
    c.pop("PROPERTY", None)
    lines = []
    for k, vals in c.items():
        if k == "CONSTANT":
            lines += ["CONSTANTS"] + [f"  {v}" for v in vals]
        else:
            lines.append(f"{k} " + " ".join(vals))
    return {**job, "model": job["model"] + "+vacuous", "gen_text": text, "cfg_text": "\n".join(lines) + "\n"}


def passing_outputs(regime: str) -> list[dict]:
    ids = set(str(s) for s in json.load(open(ROOT / "outputs/eval_100_ids.json")))
    ids.discard("1142")
    out = []
    if regime == "reference":
        for s in sorted(ids, key=int):   # every reference with a configuration (1142 has none)
            tla, _ = R.O.gold_paths(s)
            out.append({"model": "reference", "spec_id": s, "gen": tla})
        return out
    if regime == "control":
        for m, s in CONTROLS:
            job = {"model": m, "spec_id": s,
                   "gen": ROOT / f"outputs/generations/default/{m}/{s}.tla"}
            out += [job, vacuous_control(job)]
        return out
    if regime == "default":
        for m in ["claude-opus-4-5", "gemini-2-5-pro", "gpt-5"]:
            for r in json.load(open(ROOT / f"outputs/{m}.json")):
                s = str(r["spec_id"])
                if r.get("tlc_pass") and s in ids:
                    out.append({"model": m, "spec_id": s,
                                "gen": ROOT / f"outputs/generations/default/{m}/{s}.tla"})
    else:
        for m in ["claude-opus-4-5", "gemini-2-5-pro", "gpt-5",
                  "qwen2.5-coder-32b", "llama3.3-70b", "gpt-oss-20b"]:
            for r in json.load(open(ROOT / f"outputs/cfgaware/{m}.json")):
                s = str(r["spec_id"])
                if r.get("tlc_pass") and s in ids:
                    out.append({"model": m, "spec_id": s,
                                "gen": ROOT / f"outputs/generations/cfgaware/{m}/{s}.tla"})
    return out


def guard_items(text: str) -> list[dict]:
    """Bullet conjuncts with no primed variable inside action definitions."""
    lines = text.splitlines()
    items = []
    for name, d in R.definitions(text).items():
        body = d["text"].split("==", 1)[1]
        if not (PRIMED.search(R.strip_tla_comments(body)) or "UNCHANGED" in body):
            continue
        for t in range(d["start"], d["end"]):
            line = lines[t]
            if t == d["start"]:
                m = re.search(r"==\s*(/\\)", line)
                col = m.start(1) if m else None
            else:
                stripped = line.lstrip()
                col = len(line) - len(stripped) if stripped.startswith("/\\") else None
            if col is None:
                continue
            end = t + 1
            while end < d["end"]:
                nxt = lines[end]
                if nxt.strip() and len(nxt) - len(nxt.lstrip()) <= col:
                    break
                end += 1
            chunk = "\n".join([lines[t][col + 2:]] + lines[t + 1:end])
            content = R.strip_tla_comments(chunk).strip()
            if not content or PRIMED.search(content) or "UNCHANGED" in content or content == "TRUE":
                continue
            items.append({"action": name, "line": t, "col": col, "end": end,
                          "content": content, "one_line": end == t + 1})
    return items


ROR = {"<": "<=", "<=": "<", ">": ">=", ">=": ">", "#": "=", "/=": "=", "\\leq": "<", "\\geq": ">"}
ROR_RE = re.compile(r"(?<=\s)(<=|>=|<|>|#|/=|\\leq|\\geq)(?=\s)")
AOR_RE = re.compile(r"(?<=[\w)\]])(\s*)([+-])(\s*)(?=[\w(])")
IF_RE = re.compile(r"\bIF\b(.+?)\bTHEN\b")


def operator_mutants(text: str, protected: set[str]) -> list[dict]:
    """Relational / arithmetic operator flips and IF-condition negation, one occurrence per
    mutant, inside action definitions and Init, never inside a checked property."""
    lines = text.splitlines()
    out = []
    for name, d in R.definitions(text).items():
        if name in protected:
            continue
        body = d["text"].split("==", 1)[1]
        is_action = PRIMED.search(R.strip_tla_comments(body)) or "UNCHANGED" in body
        if not (is_action or name == "Init"):
            continue
        for t in range(d["start"], d["end"]):
            line = lines[t]
            code_end = min([i for i in (line.find("\\*"), line.find("(*")) if i >= 0] or [len(line)])
            lo = line.find("==") + 2 if t == d["start"] else 0
            for rx, op in ((ROR_RE, "flip_comparison"), (AOR_RE, "flip_arithmetic"), (IF_RE, "negate_if")):
                for m in rx.finditer(line):
                    if m.start() < lo or m.end() > code_end:
                        continue
                    if op == "flip_comparison":
                        new = line[:m.start()] + ROR[m.group(1)] + line[m.end():]
                    elif op == "flip_arithmetic":
                        sign = "-" if m.group(2) == "+" else "+"
                        new = line[:m.start()] + m.group(1) + sign + m.group(3) + line[m.end():]
                    else:
                        new = line[:m.start()] + "IF ~(" + m.group(1).strip() + ") THEN" + line[m.end():]
                    out.append({"op": op, "action": name, "guard": line.strip()[:120],
                                "text": "\n".join(lines[:t] + [new] + lines[t + 1:]) + "\n"})
    return out


def mutants(text: str, protected: set[str] = frozenset()) -> list[dict]:
    lines = text.splitlines()
    out = []
    for it in guard_items(text):
        t, col, end = it["line"], it["col"], it["end"]
        head = lines[t][:col + 2]
        dropped = lines[:t] + [head + " TRUE"] + [""] * (end - t - 1) + lines[end:]
        out.append({"op": "drop_guard", "action": it["action"], "guard": it["content"][:120],
                    "text": "\n".join(dropped) + "\n"})
        if it["one_line"]:
            expr = R.strip_tla_comments(lines[t][col + 2:]).strip()
            neg = lines[:t] + [head + " ~(" + expr + ")"] + lines[t + 1:]
            out.append({"op": "negate_guard", "action": it["action"], "guard": it["content"][:120],
                        "text": "\n".join(neg) + "\n"})
    out += operator_mutants(text, set(protected))
    return out[:MAX_MUTANTS]


def evaluate(job: dict) -> dict:
    tla, cfg = R.O.gold_paths(job["spec_id"])
    cfg_text = job.get("cfg_text") or cfg.read_text(errors="replace")
    gen = job.get("gen_text") or job["gen"].read_text(errors="replace")
    checks = R.checked_names(cfg_text)
    named = checks["INVARIANT"] + checks["PROPERTY"]
    base = R.run_tlc_on(gen, tla, cfg_text)
    rec = {"model": job["model"], "spec_id": job["spec_id"], "checks": checks, "is_fixture": job["spec_id"] in FIXTURES,
           "baseline": base, "mutants": []}
    if base["status"] != "pass":
        rec["verdict"] = "baseline_not_pass"
        return rec
    for mu in mutants(gen, set(named)):
        res = R.run_tlc_on(mu["text"], tla, cfg_text, timeout=60)
        st = res["status"]
        if st in ("invariant_violated", "property_violated"):
            outcome = "killed_property"
        elif st == "deadlock":
            outcome = "killed_deadlock"
        elif st == "pass":
            outcome = ("survived_same" if res.get("distinct") == base.get("distinct")
                       else "survived_changed")
        else:
            outcome = "invalid"
        rec["mutants"].append({k: mu[k] for k in ("op", "action", "guard")} |
                              {"outcome": outcome, "tlc": res})
    c = Counter(m["outcome"] for m in rec["mutants"])
    rec["counts"] = dict(c)
    if not named:
        rec["verdict"] = "no_named_property"
    elif c["killed_property"]:
        rec["verdict"] = "load_bearing"
    elif c["killed_deadlock"]:
        rec["verdict"] = "deadlock_only"
    elif c["survived_changed"]:
        rec["verdict"] = "not_load_bearing"
    else:
        rec["verdict"] = "inconclusive"
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--regime", choices=["default", "cfgaware", "reference", "control"], default="default")
    ap.add_argument("--workers", type=int, default=6)
    a = ap.parse_args()

    jobs = passing_outputs(a.regime)
    with ThreadPoolExecutor(a.workers) as ex:
        recs = sorted(ex.map(evaluate, jobs), key=lambda r: (r["model"], int(r["spec_id"])))

    dest = ROOT / "outputs/rerun"; dest.mkdir(parents=True, exist_ok=True)
    json.dump(recs, open(dest / f"mutation_{a.regime}.json", "w"), indent=2)

    print(f"regime={a.regime}: {len(recs)} passing outputs")
    for r in recs:
        print(f"  {r['model']:16s} {r['spec_id']:5s} {r['verdict']:18s} "
              f"checks={r['checks']['INVARIANT'] + r['checks']['PROPERTY']} mutants={r.get('counts', {})}")
    v = Counter(r["verdict"] for r in recs)
    print("verdicts:", dict(v))
    by_model = {}
    for r in recs:
        by_model.setdefault(r["model"], Counter())[r["verdict"]] += 1
    for m, c in by_model.items():
        print(f"  {m}: {dict(c)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
