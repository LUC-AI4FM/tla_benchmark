#!/usr/bin/env python3
"""Re-triage the REVIEW pile (SANY-pass but TLC-failed) with three fixes:

  1. STRICT config matching - a .cfg is only used if every operator name it
     references (SPECIFICATION/INIT/NEXT/INVARIANT/PROPERTY targets and
     substitution right-hand sides) is actually defined in the staged module.
     Kills wrong-cfg artifacts (e.g. KnuthYao.tla <- SimKnuthYao.cfg).
  2. -deadlock OFF - many valid specs terminate; deadlock is not a defect here.
  3. Full TLC error classification - separates intentional counterexamples
     (puzzle specs whose invariant is violated by design) from real failures.

Input:  data/dataset_manifest/review.json
Output: outputs/review_triage/<ts>/{per_spec.jsonl, summary.json}

  python scripts/review_triage.py --tlc-timeout 30
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from utils import get_logger, load_json  # noqa: E402
from validator import _find_java, _find_tla2tools  # noqa: E402
import roundtrip_fidelity as F  # noqa: E402

logger = get_logger("review_triage")

# ---- strict cfg validation ------------------------------------------------- #
_DEF = re.compile(r"^\s*([A-Za-z_]\w*)\s*(?:\([^)]*\))?\s*==", re.MULTILINE)
_DECL = re.compile(r"^\s*(?:CONSTANTS?|VARIABLES?)\s+(.+)$", re.MULTILINE)
_CFG_ENTRY = re.compile(
    r"^\s*(?:SPECIFICATION|INIT|NEXT|INVARIANTS?|PROPERTIES|PROPERTY|VIEW|SYMMETRY)\s+(.+)$",
    re.MULTILINE | re.IGNORECASE)
_CFG_SUBST = re.compile(r"^\s*([A-Za-z_]\w*)\s*<-\s*([A-Za-z_]\w*)", re.MULTILINE)
_IDENT = re.compile(r"[A-Za-z_]\w*")


def reachable_closure(main_tla: Path) -> list[Path]:
    """Files in the module-under-test's EXTENDS/INSTANCE closure (within the same
    staging dir). Excludes unrelated siblings (e.g. *_MC.tla wrappers that the
    base module does not reference) so their defs don't falsely validate a cfg."""
    wd = main_tla.parent
    seen: set[str] = set()
    out: list[Path] = []
    pending = [main_tla.stem]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        f = wd / f"{name}.tla"
        if not f.exists():
            continue
        out.append(f)
        pending.extend(F._referenced_modules(f.read_text(encoding="utf-8", errors="replace")))
    return out


def defined_names(files: list[Path]) -> set[str]:
    """Operator/constant/variable names defined across the given module files."""
    names: set[str] = set()
    for tla in files:
        txt = tla.read_text(encoding="utf-8", errors="replace")
        names.update(_DEF.findall(txt))
        for decl in _DECL.findall(txt):
            names.update(_IDENT.findall(decl.split("\\*")[0]))
    return names


def cfg_referenced_names(cfg_text: str) -> set[str]:
    """Operator names a cfg expects the module to define."""
    refs: set[str] = set()
    for line in _CFG_ENTRY.findall(cfg_text):
        refs.update(_IDENT.findall(line.split("\\*")[0]))
    for _lhs, rhs in _CFG_SUBST.findall(cfg_text):
        refs.add(rhs)  # substitution target must be defined in the module
    return refs


# CONSTANT names the cfg assigns a value (LHS of `=` or `<-`, anywhere in cfg).
_CFG_ASSIGN = re.compile(r"^\s*([A-Za-z_]\w*)\s*(?:=|<-)", re.MULTILINE)
# CONSTANT(S) the module declares (in the main module file).
_MODULE_CONSTS = re.compile(r"^\s*CONSTANTS?\s+(.+)$", re.MULTILINE)


def module_constants(main_text: str) -> set[str]:
    consts: set[str] = set()
    for decl in _MODULE_CONSTS.findall(main_text):
        # strip comments / operator-arity markers like _(_)
        for tok in decl.split("\\*")[0].split(","):
            m = re.match(r"\s*([A-Za-z_]\w*)", tok)
            if m:
                consts.add(m.group(1))
    return consts


def cfg_assigned_constants(cfg_text: str) -> set[str]:
    return set(_CFG_ASSIGN.findall(cfg_text))


def find_valid_cfg(module_stem: str, real_dir: Path, workdir: Path,
                   main_text: str) -> Path | None:
    """Pick a cfg that genuinely drives THIS module: every operator name it
    references is defined, AND every CONSTANT the module declares is assigned.
    Prefer same-stem, then *_MC variants. Returns staged cfg path, else None."""
    defined = defined_names(reachable_closure(workdir / f"{module_stem}.tla"))
    needed_consts = module_constants(main_text)
    cfgs = sorted(real_dir.glob("*.cfg"),
                  key=lambda c: (c.stem != module_stem,
                                 not c.stem.endswith("_MC"), c.name))
    for cfg in cfgs:
        text = cfg.read_text(encoding="utf-8", errors="replace")
        refs = cfg_referenced_names(text)
        if not refs or not refs.issubset(defined):
            continue
        if not needed_consts.issubset(cfg_assigned_constants(text)):
            continue  # cfg leaves one of the module's constants unassigned
        staged = workdir / cfg.name
        if not staged.exists():
            staged.write_text(text, encoding="utf-8")
        return staged
    return None


# ---- TLC with -deadlock off ------------------------------------------------ #
def run_tlc_nodeadlock(tla: Path, cfg: Path, timeout: int) -> dict:
    cmd = [_find_java(), "-cp", _find_tla2tools(), "tlc2.TLC",
           "-config", cfg.name, "-deadlock", tla.name]
    try:
        r = subprocess.run(cmd, cwd=str(tla.parent), capture_output=True,
                           text=True, timeout=timeout)
        return {"rc": r.returncode, "out": r.stdout, "err": r.stderr, "timeout": False}
    except subprocess.TimeoutExpired:
        return {"rc": -1, "out": "", "err": "timeout", "timeout": True}


def classify(res: dict) -> str:
    if res["timeout"]:
        return "timeout"
    out = res["out"]
    errs = [l for l in out.splitlines() if l.startswith("Error:")]
    if res["rc"] == 0 and not errs:
        return "pass"
    blob = " ".join(errs).lower()
    if "is violated" in blob and "invariant" in blob:
        return "invariant_violated"      # counterexample found (may be intentional)
    if "is violated" in blob or "property" in blob:
        return "property_violated"       # temporal/property counterexample
    if "deadlock" in blob:
        return "deadlock_remaining"      # should be rare with -deadlock off
    if "evaluating assumption" in blob or "assumption" in blob:
        return "assumption_failed"
    if ("undefined identifier" in blob or "not assigned a value" in blob
            or "does not appear" in blob or "substitutes for" in blob):
        return "config_error"
    if "unexpected exception" in blob or "java.lang" in blob:
        return "runtime_exception"
    return "other_error" if errs else "no_error_line"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tlc-timeout", type=int, default=30)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    review = load_json(REPO_ROOT / "data" / "dataset_manifest" / "review.json")
    if args.limit:
        review = review[: args.limit]
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = Path(args.out) if args.out else REPO_ROOT / "outputs" / "review_triage" / stamp
    out_dir.mkdir(parents=True, exist_ok=True)
    logger.info("triaging %d review specs -> %s", len(review), out_dir)

    rows: list[dict] = []
    with (out_dir / "per_spec.jsonl").open("w", encoding="utf-8") as fh:
        for i, r in enumerate(review, 1):
            tla = REPO_ROOT / r["tla_path"]
            with tempfile.TemporaryDirectory(prefix="triage_") as tmp:
                wd = Path(tmp)
                main_text = tla.read_text(encoding="utf-8", errors="replace")
                F._copy_siblings(tla.parent, wd)
                F.copy_dependencies(main_text, tla.parent, wd)
                cfg = find_valid_cfg(tla.stem, tla.parent, wd, main_text)
                if cfg is None:
                    outcome = "no_valid_cfg"   # -> belongs in SILVER, not a failure
                else:
                    outcome = classify(run_tlc_nodeadlock(wd / tla.name, cfg, args.tlc_timeout))
            row = {**{k: r[k] for k in ("spec_id", "tla_path", "repo", "complexity_tier")},
                   "valid_cfg": cfg.name if cfg else None, "outcome": outcome}
            rows.append(row)
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")
            fh.flush()
            if i % 25 == 0 or i == len(review):
                logger.info("[%d/%d] outcomes: %s", i, len(review),
                            dict(Counter(x["outcome"] for x in rows)))

    counts = Counter(x["outcome"] for x in rows)
    recovered_gold = counts["pass"]
    summary = {
        "n_review": len(rows),
        "outcomes": dict(counts),
        "recovered_to_gold": recovered_gold,
        "move_to_silver_no_valid_cfg": counts["no_valid_cfg"],
        "counterexample_specs": counts["invariant_violated"] + counts["property_violated"],
        "config_errors": counts["config_error"],
        "genuine_errors": counts["runtime_exception"] + counts["other_error"] + counts["assumption_failed"],
        "by_repo_pass": {repo: sum(1 for x in rows if x["repo"] == repo and x["outcome"] == "pass")
                         for repo in sorted({x["repo"] for x in rows})},
    }
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False),
                                          encoding="utf-8")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
