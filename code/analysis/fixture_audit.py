#!/usr/bin/env python3
"""Check the evaluation set for single-state fixtures.

The paper says the 100 evaluation specs exclude every trivial fixture (a reference with a
single reachable state). This model-checks each reference with its own cfg and records the
number of distinct states. Writes outputs/rebuttal/fixture_audit.json.
"""
from __future__ import annotations
import json, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tla_lib as R

ROOT = R.ROOT


def check(s: str) -> dict:
    tla, cfg = R.O.gold_paths(s)
    if not cfg or not cfg.exists():
        return {"spec_id": s, "status": "no_cfg"}
    res = R.run_tlc_on(tla.read_text(errors="replace"), tla, cfg.read_text(errors="replace"), timeout=300)
    return {"spec_id": s, "file": tla.name, **res}


def main() -> int:
    ids = [str(s) for s in json.load(open(ROOT / "outputs/eval_100_ids.json"))]
    with ThreadPoolExecutor(4) as ex:
        recs = sorted(ex.map(check, ids), key=lambda r: int(r["spec_id"]))
    dest = ROOT / "outputs/rerun"; dest.mkdir(parents=True, exist_ok=True)
    json.dump(recs, open(dest / "fixture_audit.json", "w"), indent=2)
    single = [r for r in recs if r.get("distinct") == 1]
    other = [r for r in recs if r.get("status") != "pass"]
    print(f"{len(recs)} references checked")
    print(f"single-state references: {len(single)}")
    for r in single:
        print(f"  {r['spec_id']:5s} {r['file']}")
    print(f"references that do not pass their own cfg: {len(other)}")
    for r in other:
        print(f"  {r['spec_id']:5s} {r.get('file')} {r['status']} {r.get('error', '')[:100]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
