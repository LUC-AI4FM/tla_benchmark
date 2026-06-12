#!/usr/bin/env python3
"""Measure how many raw-corpus specs pass SANY (and TLC where a cfg drives them).

Uses the same isolated-staging + dependency-flattening as the fidelity check, so
the numbers are apples-to-apples with what a reconstruction is scored against.
No GPT / no network. Each spec is verified in a throwaway temp dir.

  python scripts/corpus_health.py                 # SANY for all specs
  python scripts/corpus_health.py --tlc            # + TLC where same-stem cfg
  python scripts/corpus_health.py --limit 100      # quick sample

Writes outputs/corpus_health/<timestamp>/{per_spec.jsonl, summary.json}.
"""
from __future__ import annotations

import argparse
import json
import sys
import tempfile
from collections import defaultdict
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from utils import get_logger, load_json  # noqa: E402
import validator  # noqa: E402
import roundtrip_fidelity as F  # noqa: E402

logger = get_logger("corpus_health")


def classify_tlc(c: dict) -> str:
    """pass | fail | timeout | no_cfg | skipped_sany_failed | disabled."""
    status = c.get("original_tlc_status")
    if status != "ran":
        return status or "not_run"
    if c.get("original_tlc_pass"):
        return "pass"
    err = (c.get("original_tlc_error") or "").lower()
    return "timeout" if "timeout" in err else "fail"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tlc", action="store_true", help="also run TLC where a cfg drives the module")
    ap.add_argument("--tlc-timeout", type=int, default=120, help="per-spec TLC cap in seconds")
    ap.add_argument("--limit", type=int, default=None, help="only first N specs (debug)")
    ap.add_argument("--ids-file", default=None, help="JSON list of spec_ids to check (subset)")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    validator.TLC_TIMEOUT = args.tlc_timeout

    index = {int(k): v for k, v in load_json(REPO_ROOT / "data" / "index.json").items()}
    ids = sorted(index)
    if args.ids_file:
        wanted = set(load_json(args.ids_file))
        ids = [i for i in ids if i in wanted]
    if args.limit:
        ids = ids[: args.limit]

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = Path(args.out) if args.out else REPO_ROOT / "outputs" / "corpus_health" / stamp
    out_dir.mkdir(parents=True, exist_ok=True)
    logger.info("checking %d specs -> %s (tlc=%s)", len(ids), out_dir, args.tlc)

    rows: list[dict] = []
    with (out_dir / "per_spec.jsonl").open("w", encoding="utf-8") as fh:
        for i, sid in enumerate(ids, 1):
            rec = index[sid]
            tla = REPO_ROOT / rec["tla_path"]
            with tempfile.TemporaryDirectory(prefix="health_") as tmp:
                c = F.verify_original(tla, run_tlc_check=args.tlc, workdir=Path(tmp))
            row = {
                "spec_id": sid,
                "complexity_tier": rec.get("complexity_tier", "basic"),
                "repo": rec["tla_path"].split("/")[2] if "/" in rec["tla_path"] else "?",
                "tla_path": rec["tla_path"],
                "sany_pass": c["original_sany_pass"],
                "tlc_outcome": classify_tlc(c) if args.tlc else "disabled",
                "tlc_cfg": c.get("original_tlc_cfg"),
                "unresolved_deps": c.get("original_unresolved_deps") or [],
            }
            rows.append(row)
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")
            fh.flush()
            if i % 50 == 0 or i == len(ids):
                np = sum(r["sany_pass"] for r in rows)
                logger.info("[%d/%d] SANY pass so far: %d (%.1f%%)",
                            i, len(ids), np, 100 * np / len(rows))

    n = len(rows)
    sany_pass = sum(r["sany_pass"] for r in rows)
    tlc_counts: dict = defaultdict(int)
    for r in rows:
        tlc_counts[r["tlc_outcome"]] += 1

    def _by(key: str) -> dict:
        agg: dict = defaultdict(lambda: [0, 0])
        for r in rows:
            agg[r[key]][0] += r["sany_pass"]
            agg[r[key]][1] += 1
        return {k: {"sany_pass": a, "n": b, "rate": round(a / b, 3)}
                for k, (a, b) in sorted(agg.items())}

    tlc_ran = tlc_counts["pass"] + tlc_counts["fail"] + tlc_counts["timeout"]
    # The "clean" set = parses AND (model-checks OR has no cfg to check / timed out
    # but didn't actually violate). The strict benchmark-ready set is sany_pass
    # plus tlc_outcome in {pass, no_cfg}.
    benchmark_ready = sum(
        1 for r in rows
        if r["sany_pass"] and r["tlc_outcome"] in ("pass", "no_cfg", "disabled"))
    summary = {
        "n_specs": n,
        "sany_pass": sany_pass,
        "sany_pass_rate": round(sany_pass / n, 3) if n else None,
        "tlc_enabled": args.tlc,
        "tlc_timeout_s": args.tlc_timeout,
        "tlc_outcomes": dict(tlc_counts),
        "tlc_pass_rate_where_run": round(tlc_counts["pass"] / tlc_ran, 3) if tlc_ran else None,
        "benchmark_ready": benchmark_ready,
        "benchmark_ready_rate": round(benchmark_ready / n, 3) if n else None,
        "sany_by_tier": _by("complexity_tier"),
        "sany_by_repo": _by("repo"),
    }
    (out_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
