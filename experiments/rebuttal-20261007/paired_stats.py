"""Exact McNemar tests between the three commercial models and 95% bootstrap intervals for their
default correct rates, from the released per-specification grades (outputs/<model>.json).

Run from the repository root:  python experiments/rebuttal-20261007/paired_stats.py
Writes experiments/rebuttal-20261007/paired_stats.json.
"""
import json, math, random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ids = [str(x) for x in json.loads((ROOT / "outputs/eval_100_ids.json").read_text())]
files = {"Claude Opus 4.5": "claude-opus-4-5", "Gemini-2.5-pro": "gemini-2-5-pro", "GPT-5": "gpt-5"}
ok = {m: {str(r["spec_id"]): r["label"] == "correct"
          for r in json.loads((ROOT / f"outputs/{f}.json").read_text())} for m, f in files.items()}

def mcnemar(a, b):
    only_a = sum(ok[a][s] and not ok[b][s] for s in ids)
    only_b = sum(ok[b][s] and not ok[a][s] for s in ids)
    n = only_a + only_b
    p = min(1.0, 2 * sum(math.comb(n, k) for k in range(min(only_a, only_b) + 1)) / 2 ** n) if n else 1.0
    return {"a": a, "b": b, "only_a_correct": only_a, "only_b_correct": only_b, "exact_p": p}

rng = random.Random(0)
boot = {}
for m in files:
    v = [ok[m][s] for s in ids]
    draws = sorted(sum(rng.choice(v) for _ in v) for _ in range(10000))
    boot[m] = {"correct": sum(v), "ci95": [draws[250], draws[9749]]}

names = list(files)
tests = [mcnemar(names[i], names[j]) for i in range(3) for j in range(i + 1, 3)]
out = {"mcnemar": tests, "bootstrap_10000_seed0": boot}
(ROOT / "experiments/rebuttal-20261007/paired_stats.json").write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
