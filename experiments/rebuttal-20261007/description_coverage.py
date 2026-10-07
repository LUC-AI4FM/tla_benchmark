"""Length of each declarative description set, and the share of the identifiers named in the
reference configuration that each description mentions, over the 100 evaluation specifications.

Run from the repository root:  python experiments/rebuttal-20261007/description_coverage.py
Writes experiments/rebuttal-20261007/description_coverage.json.
"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "code" / "analysis"))
import grading as G

ids = [str(x) for x in json.loads((ROOT / "outputs/eval_100_ids.json").read_text())]
sets = {"gpt": "declarative_gpt", "claude": "declarative_claude"}
words = {k: [] for k in sets}
share = {k: [] for k in sets}
per_item = []
for sid in ids:
    _, cfg = G.gold_paths(sid)
    names = set()
    if cfg is not None:
        names = {n for n in G.cfg_names(cfg.read_text(errors="replace")).replace(",", " ").split()
                 if re.fullmatch(r"[A-Za-z_]\w*", n)}
    row = {"spec_id": sid, "cfg_names": sorted(names)}
    for k, folder in sets.items():
        text = (ROOT / "descriptions" / folder / f"{sid}.txt").read_text(errors="replace")
        words[k].append(len(text.split()))
        row[f"{k}_words"] = len(text.split())
        if names:
            hit = [n for n in names if re.search(r"\b" + re.escape(n) + r"\b", text)]
            share[k].append(len(hit) / len(names))
            row[f"{k}_names_mentioned"] = sorted(hit)
    per_item.append(row)

summary = {k: {"mean_words": round(sum(words[k]) / len(words[k]), 1),
               "items_with_cfg_names": len(share[k]),
               "mean_share_of_cfg_names_mentioned": round(sum(share[k]) / len(share[k]), 3)}
           for k in sets}
out = ROOT / "experiments/rebuttal-20261007/description_coverage.json"
out.write_text(json.dumps({"summary": summary, "items": per_item}, indent=1))
print(json.dumps(summary, indent=1))
