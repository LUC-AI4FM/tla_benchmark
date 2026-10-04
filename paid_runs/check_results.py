#!/usr/bin/env python3
"""Summarize every run under results/: completeness, parse and correct counts per sample,
mean and spread across samples, pass@k, empty answers and finish reasons."""
import json
from collections import Counter, defaultdict
from pathlib import Path
from statistics import mean, pstdev

HERE = Path(__file__).resolve().parent
ids = [str(s) for s in json.load(open(HERE.parent / "outputs" / "eval_100_ids.json"))]

for d in sorted((HERE / "results").glob("*/results.json")):
    rows = json.load(open(d))
    by_sample = defaultdict(dict)
    for r in rows:
        by_sample[r["sample"]][r["spec_id"]] = r
    print(f"== {d.parent.name}")
    for k in sorted(by_sample):
        got = by_sample[k]
        missing = [s for s in ids if s not in got]
        p = sum(bool(r["sany_pass"]) for r in got.values())
        c = sum(bool(r["tlc_pass"]) for r in got.values())
        print(f"   sample {k}: {len(got)}/100 graded, parse {p}, correct {c}"
              + (f", MISSING {len(missing)}: {missing[:8]}" if missing else ""))
    complete = [k for k in by_sample if len(by_sample[k]) == len(ids)]
    if len(complete) > 1:
        cs = [sum(bool(r["tlc_pass"]) for r in by_sample[k].values()) for k in complete]
        pk = sum(any(by_sample[k][s]["tlc_pass"] for k in complete) for s in ids)
        print(f"   over {len(complete)} complete samples: correct mean {mean(cs):.1f}, "
              f"spread (sd) {pstdev(cs):.1f}, range {min(cs)}-{max(cs)}, pass@{len(complete)} {pk}")
    print(f"   empty answers {sum(r['empty_response'] for r in rows)}, finish reasons "
          f"{dict(Counter(str(r['finish_reason']) for r in rows))}")
