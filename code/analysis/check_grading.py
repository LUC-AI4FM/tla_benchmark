#!/usr/bin/env python3
"""Re-grade every released generated specification and compare with the released verdict.

Covers the default-regime outputs of the three frontier models and the configuration-aware
outputs of all six models (900 specifications). Reports every disagreement.

Usage (from the release root):
    python code/analysis/check_grading.py [--workers 8]
"""
from __future__ import annotations
import argparse, json, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import grading as G

OUT = G.REL / "outputs"
FRONTIER = ["claude-opus-4-5", "gemini-2-5-pro", "gpt-5"]
OPEN = ["qwen2.5-coder-32b", "llama3.3-70b", "gpt-oss-20b"]


def jobs():
    for m in FRONTIER:
        for r in json.load(open(OUT / f"{m}.json")):
            yield "default", m, str(r["spec_id"]), r
    for m in FRONTIER + OPEN:
        for r in json.load(open(OUT / "cfgaware" / f"{m}.json")):
            yield "cfgaware", m, str(r["spec_id"]), r


def check(job):
    regime, m, s, rec = job
    tla, _ = G.gold_paths(s)
    gen = (OUT / "generations" / regime / m / f"{s}.tla").read_text(errors="replace")
    g = G.grade_clean(gen, tla)
    want = (bool(rec.get("sany_pass")), bool(rec.get("tlc_pass")))
    got = (g["sany_pass"], g["tlc_pass"])
    return regime, m, s, want, got


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=8)
    a = ap.parse_args()
    js = list(jobs())
    with ThreadPoolExecutor(a.workers) as ex:
        res = list(ex.map(check, js))
    bad = [r for r in res if r[3] != r[4]]
    print(f"re-graded {len(res)} released outputs; {len(res) - len(bad)} match the released verdict")
    for regime, m, s, want, got in bad:
        print(f"  MISMATCH {regime:8s} {m:18s} {s:5s} released sany/tlc={want} regraded={got}")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
