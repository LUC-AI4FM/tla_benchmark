"""Controls for the reference check (code/analysis/reference_check.py), on specification 930
(HourClock). The passing Claude Opus 4.5 output is changed in two ways:
  reset   - the clock may also reset to 1 at any step (adds behavior the reference lacks)
  start1  - the clock may only start at 1 (omits initial states the reference allows)
The first check (generated implies reference) must fail for `reset`; the second check
(reference implies generated) must fail for `start1`; the unchanged output must pass both.

Run from the repository root:  python experiments/rebuttal-20261007/refcheck_controls.py
Writes experiments/rebuttal-20261007/refcheck_controls.json and the two control modules.
"""
import json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "experiments/rebuttal-20261007"
sys.path.insert(0, str(ROOT / "code" / "analysis"))
import reference_check as RC

gen = ROOT / "outputs/generations/default/claude-opus-4-5/930.tla"
src = gen.read_text()
nxt = "HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1"
ini = r"HCini == hr \in (1 .. 12)"
assert nxt in src and ini in src
variants = {
    "unchanged": gen,
    "reset": src.replace(nxt, "HCnxt == (hr' = IF hr # 12 THEN hr + 1 ELSE 1) \\/ (hr' = 1)"),
    "start1": src.replace(ini, "HCini == hr = 1"),
}
out = []
for name, v in variants.items():
    path = v if isinstance(v, Path) else HERE / "controls" / f"930_{name}.tla"
    if not isinstance(v, Path):
        path.parent.mkdir(exist_ok=True)
        path.write_text(v)
    r = RC.evaluate({"model": f"control_{name}", "spec_id": "930", "gen": path})
    out.append({"control": name, "module": str(path.relative_to(ROOT)),
                "first_check": r["forward"], "second_check": r["reverse"], "verdict": r["behavior"]})
    print(out[-1])
(HERE / "refcheck_controls.json").write_text(json.dumps(out, indent=1))
