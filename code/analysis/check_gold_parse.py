#!/usr/bin/env python3
"""Parse every gold reference with SANY exactly as the grader stages it (release layout).

A gold reference fails here when it imports a module that the release does not contain.
Writes outputs/rerun/gold_parse.json and prints the failures.

Usage (from the release root):
    python code/analysis/check_gold_parse.py [--workers 8]
"""
from __future__ import annotations
import argparse, json, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import grading as G


def check(tla: Path) -> dict:
    text = tla.read_text(errors="replace")
    mod = G.module_name(text)
    with tempfile.TemporaryDirectory(prefix="goldparse_") as d:
        d = Path(d)
        G._stage_siblings_by_module(tla.parent, d)
        G.copy_dependencies(text, tla.parent, d)
        r = G.run_sany(str(d / f"{mod}.tla"), search_paths=[])
    first = next((l for l in r["stdout"].splitlines() if "rror" in l or "Cannot find" in l), "")
    return {"spec": tla.name, "parses": bool(r["passed"]), "error": first[:200]}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=8)
    a = ap.parse_args()
    ids = set(json.load(open(G.REL / "outputs/eval_100_ids.json")))
    with ThreadPoolExecutor(a.workers) as ex:
        res = list(ex.map(check, sorted(G.GOLD.glob("*.tla"))))
    out = G.REL / "outputs/rerun"; out.mkdir(parents=True, exist_ok=True)
    json.dump(res, open(out / "gold_parse.json", "w"), indent=1)
    bad = [r for r in res if not r["parses"]]
    print(f"{len(res) - len(bad)} of {len(res)} gold references parse in the release layout")
    for r in bad:
        tag = " (evaluation set)" if r["spec"].split("_")[0] in ids else ""
        print(f"  {r['spec']}{tag}: {r['error']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
