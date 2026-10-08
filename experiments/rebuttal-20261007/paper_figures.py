"""Numbers behind the figures and tables of the paper that two_model_numbers.py does not print:
checks of the passing specifications for each model, specification sizes, description lengths
and the share of configuration names that each declarative description mentions.

Run from the repository root:  python experiments/rebuttal-20261007/paper_figures.py
Writes experiments/rebuttal-20261007/paper_figures.json.
"""
import glob, json, os, re, statistics
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "outputs"
load = lambda *p: json.loads(OUT.joinpath(*p).read_text())
ids = [str(x) for x in load("eval_100_ids.json")]
man = {str(json.loads(l)["spec_id"]): json.loads(l) for l in open(ROOT / "manifest.jsonl")}
single = {r["spec_id"] for r in load("audit", "fixture_audit.json") if r.get("distinct") == 1}
out = {}

# checks of the default passes, per model
ref = load("pass_quality", "refcheck_default.json")
hand = {(r["model"], r["spec_id"]): r["behavior"] for r in load("pass_quality", "audit12.json")}
mut = {(r["model"], r["spec_id"]): r for r in load("pass_quality", "mutation_default.json")}
aud = {(r["model"], r["spec_id"]): r for r in load("_pass_audit.json")}
for key in ["claude-opus-4-5", "gpt-5"]:
    res = {str(r["spec_id"]): r for r in load(f"{key}.json")}
    passes = [s for s in ids if res[s]["label"] == "correct"]
    rows = [r for r in ref if r["model"] == key]
    beh = [hand.get((key, r["spec_id"])) or r.get("behavior") for r in rows]
    beh = Counter(b if b in ("same_behaviors", "omits_reference_behavior") else "undecided" for b in beh)
    out[key] = {
        "pass_tlc": len(passes),
        "reference_comparison": dict(beh),
        "same_behaviors_on_single_state_references": sum(
            1 for r, b in zip(rows, [hand.get((key, r["spec_id"])) or r.get("behavior") for r in rows])
            if b == "same_behaviors" and r["spec_id"] in single),
        "behavior_change_test": dict(Counter(mut[(key, s)]["verdict"] for s in passes)),
        "reference_properties": dict(Counter(r["ref_props"] for r in rows)),
        "exercises_behavior": sum(1 for s in passes if not aud[(key, s)]["degenerate"] and aud[(key, s)]["real_props"] > 0),
    }

# one row per default pass, for the per-specification figure
out["passing_specs"] = []
for key in ["claude-opus-4-5", "gpt-5"]:
    res = {str(r["spec_id"]): r for r in load(f"{key}.json")}
    refrow = {r["spec_id"]: r for r in ref if r["model"] == key}
    for s in ids:
        if res[s]["label"] != "correct":
            continue
        r = refrow[s]
        out["passing_specs"].append({
            "model": key, "spec_id": s, "module": os.path.basename(man[s]["source_path"])[:-4],
            "difficulty": man[s]["complexity"], "reachable_states": mut[(key, s)]["baseline"].get("distinct"),
            "behavior": hand.get((key, s)) or r.get("behavior"), "ref_props": r["ref_props"],
            "behavior_change": mut[(key, s)]["verdict"],
            "exercises_behavior": not aud[(key, s)]["degenerate"] and aud[(key, s)]["real_props"] > 0,
        })

# sizes: lines of TLA+ without blank lines and comments
def loc(path):
    text = re.sub(r"\(\*.*?\*\)", "", open(path, errors="ignore").read(), flags=re.S)
    return sum(1 for l in text.splitlines() if l.strip() and not l.strip().startswith("\\*"))
size = {}
for f in glob.glob(str(ROOT / "specs" / "**" / "*.tla"), recursive=True):
    b = os.path.basename(f)
    if re.match(r"^\d+_", b) and b.split("_")[0] in man:
        size[b.split("_")[0]] = loc(f)
def quart(v):
    v = sorted(v); n = len(v)
    return {"q1": v[int(0.25 * (n - 1))], "median": statistics.median(v), "q3": v[int(0.75 * (n - 1))], "n": n}
out["size"] = {t: quart([size[s] for s in size if man[s]["tier"] == t]) for t in ("gold", "silver")}
out["size_benchmark"] = {t: quart([size[s] for s in ids if man[s]["complexity"] == t]) for t in ("basic", "intermediate", "advanced")}

# description lengths in words
out["description_words"] = {d: quart([len((ROOT / "descriptions" / d / f"{s}.txt").read_text().split()) for s in man])
                            for d in ("declarative_gpt", "declarative_claude", "intent_gpt", "intent_claude")}

# share of configuration names mentioned (from description_coverage.json)
cov = json.loads((ROOT / "experiments/rebuttal-20261007/description_coverage.json").read_text())
bins = {k: Counter() for k in ("gpt", "claude")}
for item in cov["items"]:
    n = len(item["cfg_names"])
    if not n:
        continue
    for k in bins:
        share = len(item.get(f"{k}_names_mentioned", [])) / n
        bins[k]["none" if share == 0 else "under half" if share < 0.5 else "half or more" if share < 1 else "all"] += 1
out["name_coverage"] = {k: dict(v) for k, v in bins.items()}

(ROOT / "experiments/rebuttal-20261007/paper_figures.json").write_text(json.dumps(out, indent=1))
print(json.dumps(out, indent=1))
