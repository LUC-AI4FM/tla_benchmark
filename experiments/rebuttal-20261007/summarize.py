"""Recompute the repeated-sample and cross-provider numbers reported in the rebuttal from the
graded records. GPT-5 and open-model runs: results/<run>/results.json in this folder.
Claude Opus 4.5 runs: experiments/opus45-20261004/evidence/<A1|A2|A3>/*/author-grade.json.

Run from the repository root:  python experiments/rebuttal-20261007/summarize.py
"""
import json
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "experiments/rebuttal-20261007"

def tally(records):
    by_sample = defaultdict(list)
    for r in records:
        by_sample[r["sample"]].append(r)
    for rows in by_sample.values():
        assert len({r["spec_id"] for r in rows}) == len(rows) == 100, "expected 100 specifications per sample"
    solved = {r["spec_id"] for r in records if r["tlc_pass"]}
    return {s: sum(bool(r["tlc_pass"]) for r in rows) for s, rows in sorted(by_sample.items())}, len(solved)

def ours(run):
    return json.loads((HERE / "results" / run / "results.json").read_text())

def opus(job):
    return [json.loads(p.read_text()) for p in
            sorted((ROOT / "experiments/opus45-20261004/evidence" / job).glob("*/author-grade.json"))]

def show(label, records):
    per_sample, any_pass = tally(records)
    extra = f"   solved by at least one sample: {any_pass}" if len(per_sample) > 1 else ""
    print(f"{label:62s} correct per sample {list(per_sample.values())}{extra}")

print("Repeated samples (GPT-written declarative descriptions, default setting)")
show("  Claude Opus 4.5, A3, samples 0-4", opus("A3"))
show("  GPT-5, B2, samples 1-4 (sample 0 is outputs/gpt-5.json)", ours("gpt-5__default__gptdesc"))
print("Claude-written declarative descriptions, default setting")
show("  Claude Opus 4.5, A2", opus("A2"))
show("  GPT-5, B1", ours("gpt-5__default__claudedesc"))
for m in ("qwen2.5-coder-32b", "llama3.3-70b", "gpt-oss-20b"):
    show(f"  {m}, D (release grader)", ours(f"{m}__default__claudedesc"))
print("GPT-written declarative descriptions, configuration-aware setting, 16,000 tokens")
show("  Claude Opus 4.5, A1", opus("A1"))
