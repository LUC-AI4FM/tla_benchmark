"""Build the full results matrix: every model, description set and setting, with the number of
correct outputs out of 100. Reads only files in this repository.

Sources:
  outputs/<model>.json, outputs/contamination/<open model>__clean.json   paper, default setting
  outputs/cfgaware/<model>.json                                         released configuration-aware runs
  experiments/opus45-20261004/evidence/<A1|A2|A3>/*/author-grade.json   Claude Opus 4.5 runs (PR #39)
  experiments/rebuttal-20261007/results/<run>/results.json              all other new runs

Run from the repository root:  python experiments/rebuttal-20261007/results_matrix.py
Writes experiments/rebuttal-20261007/results_matrix.md.
"""
import json
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "experiments/rebuttal-20261007"
IDS = {str(x) for x in json.loads((ROOT / "outputs/eval_100_ids.json").read_text())}

MODELS = [("Claude Opus 4.5", "claude-opus-4-5"), ("Gemini-2.5-pro", "gemini-2-5-pro"), ("GPT-5", "gpt-5"),
          ("qwen2.5-coder-32b", "qwen2.5-coder-32b"), ("llama3.3-70b", "llama3.3-70b"), ("gpt-oss-20b", "gpt-oss-20b")]
OPEN = {"qwen2.5-coder-32b", "llama3.3-70b", "gpt-oss-20b"}
COLUMNS = [("default", "gpt"), ("default", "claude"), ("default", "intent_gpt"), ("default", "intent_claude"),
           ("cfgaware", "gpt"), ("cfgaware", "claude"), ("cfgaware", "intent_gpt"), ("cfgaware", "intent_claude")]
HEAD = ["Default: GPT-written declarative", "Default: Claude-written declarative",
        "Default: intent (GPT)", "Default: intent (Claude)",
        "Config-aware: GPT-written declarative", "Config-aware: Claude-written declarative",
        "Config-aware: intent (GPT)", "Config-aware: intent (Claude)"]


def load(path):
    return json.loads(Path(path).read_text())


def correct(r):
    return r["label"] == "correct" if "label" in r else bool(r["tlc_pass"])


def count(rows, sample=None):
    rows = [r for r in rows if str(r["spec_id"]) in IDS and (sample is None or r.get("sample", 0) == sample)]
    assert len({str(r["spec_id"]) for r in rows}) == len(rows) == 100, "expected 100 items"
    return sum(correct(r) for r in rows)


def opus(job):
    return [load(p) for p in sorted((ROOT / "experiments/opus45-20261004/evidence" / job).glob("*/author-grade.json"))]


def new_run(name):
    p = HERE / "results" / name / "results.json"
    return load(p) if p.exists() else None


cell = {}
for _, key in MODELS:
    paper_default = ROOT / ("outputs/contamination/%s__clean.json" % key if key in OPEN else "outputs/%s.json" % key)
    cell[(key, "default", "gpt")] = (count(load(paper_default)), "paper")
    cell[(key, "cfgaware", "gpt")] = (count(load(ROOT / "outputs/cfgaware" / f"{key}.json")), "released")
    for mode, desc in COLUMNS:
        if (key, mode, desc) in cell:
            continue
        rows = new_run(f"{key}__{mode}__{desc}desc")
        if key == "claude-opus-4-5" and (mode, desc) == ("default", "claude"):
            rows = opus("A2")
        if rows is not None:
            cell[(key, mode, desc)] = (count(rows), "new")

lines = ["# Results matrix", "",
         "Correct outputs out of the 100 evaluation items (TLC pass). One run per cell unless noted. "
         "\"not run\" marks a combination without a run. Gemini-2.5-pro is no longer offered to new "
         "API users, so its new combinations were not run.", "",
         "| Model | " + " | ".join(HEAD) + " |", "|---" * (len(HEAD) + 1) + "|"]
for name, key in MODELS:
    row = []
    for mode, desc in COLUMNS:
        v = cell.get((key, mode, desc))
        row.append("not run" if v is None else f"{v[0]}" + (" (paper)" if v[1] == "paper" else ""))
    lines.append(f"| {name} | " + " | ".join(row) + " |")

lines += ["", "## Repeated runs (default setting, GPT-written declarative descriptions)", "",
          "| Model | Paper run | New runs | Solved by at least one new run |", "|---|---|---|---|"]
for name, rows, note in [("Claude Opus 4.5", opus("A3"), "5 new runs, A3"),
                         ("GPT-5", new_run("gpt-5__default__gptdesc"), "4 new runs, B2"),
                         ("qwen2.5-coder-32b", new_run("qwen2.5-coder-32b-t0.8__default__gptdesc"), "5 runs at temperature 0.8"),
                         ("llama3.3-70b", new_run("llama3.3-70b-t0.8__default__gptdesc"), "5 runs at temperature 0.8"),
                         ("gpt-oss-20b", new_run("gpt-oss-20b-t0.8__default__gptdesc"), "5 runs at temperature 0.8")]:
    per = defaultdict(int)
    for r in rows:
        per[r["sample"]] += bool(r["tlc_pass"])
    solved = len({r["spec_id"] for r in rows if r["tlc_pass"]})
    key = {"Claude Opus 4.5": "claude-opus-4-5", "GPT-5": "gpt-5"}.get(name, name.split(" ")[0])
    lines.append(f"| {name} | {cell[(key, 'default', 'gpt')][0]} | "
                 + ", ".join(str(per[s]) for s in sorted(per)) + f" ({note}) | {solved} |")

lines += ["", "## Other reruns", "",
          "| Run | Correct out of 100 | Files |", "|---|---|---|",
          f"| Claude Opus 4.5, configuration-aware, GPT-written declarative, 16,000 tokens (A1) | {count(opus('A1'))} | `experiments/opus45-20261004/evidence/A1/` |"]
for key in ["qwen2.5-coder-32b", "llama3.3-70b", "gpt-oss-20b"]:
    lines.append(f"| {key}, default, GPT-written declarative, rerun with the released grader (D0) | "
                 f"{count(new_run(f'{key}__default__gptdesc'))} | `results/{key}__default__gptdesc/` |")

lines += ["", "## Notes", "",
          "- The configuration-aware GPT-written column is the released run in `outputs/cfgaware/`. "
          "The Claude Opus 4.5 value there (26) used a 4,096-token limit. The A1 rerun at 16,000 tokens gave 22.",
          "- New open-model runs are graded with the released grader (`code/analysis/grading.py`), which requires "
          "the `---- MODULE Name ----` line. llama3.3-70b and gpt-oss-20b often omit it in the default setting.",
          "- The paper's default-setting values for the open models come from `outputs/contamination/`.",
          "- The temperature 0.8 open-model runs have five samples of which sample 0 is not the paper's run."]
(HERE / "results_matrix.md").write_text("\n".join(lines) + "\n")
print("\n".join(lines))
