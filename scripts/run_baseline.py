#!/usr/bin/env python3
"""Run a model baseline on the CLEANED benchmark (description -> TLA+ -> SANY/TLC).

Why this exists (not src/runner.py): runner.py is wired to the old test_split,
looks for cfgs in data/cfg/ (wrong path -> TLC never runs), and validates the
generated spec in an empty dir with no dependency staging (-> false SANY fails
on any spec that EXTENDS a local module). This runner fixes all of that by
reusing the proven staging from roundtrip_fidelity.py (copy_dependencies +
find_cfg + stage_and_verify) and the multi-backend model call from runner.py.

Grading degrades automatically: gold specs have a cfg -> SANY+TLC (pass@1);
silver specs have none -> SANY-only (syntactic validity).

  python scripts/run_baseline.py --model qwen2.5-coder-32b \
         --buckets gold_system silver_system --track declarative
  python scripts/run_baseline.py --model gpt-5.5 --buckets gold_system --track intent

Output (analyze_results.py compatible): outputs/run_<model_id>__<track>.json
"""
from __future__ import annotations

import argparse
import json
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from utils import get_logger, load_json, outputs_dir  # noqa: E402
from runner import _call_model  # multi-backend dispatch (ollama/openai/anthropic/google)
import roundtrip_fidelity as F  # noqa: E402  proven staging + validation

logger = get_logger("run_baseline")
MDIR = REPO_ROOT / "data" / "dataset_manifest"

# Description source per (provider, track). Claude has both styles for gold-system
# (134 each). GPT declarative = data/descriptions/ (all specs); GPT intent = gold only.
DESC_SOURCE = {
    ("claude", "declarative"): MDIR / "desc_claude",
    ("claude", "intent"):      MDIR / "desc_intent",
    ("gpt",    "declarative"): REPO_ROOT / "data" / "descriptions",
    ("gpt",    "intent"):      MDIR / "desc_gpt_intent",
}
PROMPT_TEMPLATE = (REPO_ROOT / "configs" / "prompts" / "nlp_to_tla.txt").read_text(encoding="utf-8")


def load_description(provider: str, track: str, sid: int) -> str | None:
    src = DESC_SOURCE.get((provider, track))
    if src is None:
        return None
    p = src / f"{sid}.txt"
    return p.read_text(encoding="utf-8").strip() if p.exists() else None


def load_specs(buckets: list[str]) -> list[dict]:
    seen, out = set(), []
    for b in buckets:
        for r in load_json(MDIR / f"{b}.json"):
            if r["spec_id"] not in seen:
                seen.add(r["spec_id"])
                r["_bucket"] = b
                out.append(r)
    return out


def run_one(spec: dict, track: str, provider: str, model_cfg: dict) -> dict:
    sid = spec["spec_id"]
    original_tla = REPO_ROOT / spec["tla_path"]
    rec = {"spec_id": sid, "model_id": model_cfg["id"], "condition": track,
           "desc_provider": provider,
           "bucket": spec.get("_bucket"), "complexity_tier": spec.get("complexity_tier", "unknown"),
           "sany_pass": False, "tlc_pass": None, "tlc_status": None,
           "pass_at_1": None, "syntactic_pass": False, "error": None}

    desc = load_description(provider, track, sid)
    if not desc:
        rec["error"] = "no_description"
        return rec
    prompt = PROMPT_TEMPLATE.replace("{description}", desc)

    try:
        out = _call_model(model_cfg, prompt)
    except Exception as exc:  # noqa: BLE001
        rec["error"] = f"model_error: {exc}"[:200]
        return rec
    rec["tokens_out"] = out.get("tokens_out", 0)

    reconstructed, module_name = F.extract_tla(out["text"])
    if not reconstructed or not module_name:
        rec["error"] = "extraction_failed"
        return rec

    # proven staging: copy siblings + resolve EXTENDS deps + find cfg, run SANY(+TLC)
    with tempfile.TemporaryDirectory(prefix="baseline_") as tmp:
        v = F.stage_and_verify(reconstructed, module_name, original_tla,
                               run_tlc_check=True, workdir=Path(tmp))
    rec["sany_pass"] = bool(v["sany_pass"])
    rec["syntactic_pass"] = bool(v["sany_pass"])
    rec["tlc_status"] = v.get("tlc_status")
    rec["tlc_pass"] = v.get("tlc_pass")
    # pass@1: gold (TLC ran) = SANY+TLC; silver (no cfg) = SANY only
    if v.get("tlc_status") == "ran":
        rec["pass_at_1"] = bool(v["sany_pass"] and v.get("tlc_pass"))
    else:
        rec["pass_at_1"] = bool(v["sany_pass"])  # no cfg -> syntactic pass is the bar
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", required=True, help="model id from configs/models.json")
    ap.add_argument("--buckets", nargs="+", default=["gold_system", "silver_system"])
    ap.add_argument("--track", default="declarative", choices=["declarative", "intent"])
    ap.add_argument("--provider", default="claude", choices=["claude", "gpt"],
                    help="which description set to use as the benchmark input")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--api-key", default="")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    if args.api_key:
        import os
        for k in ("OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GEMINI_API_KEY"):
            os.environ.setdefault(k, args.api_key)

    models = {m["id"]: m for m in load_json(REPO_ROOT / "configs" / "models.json")}
    if args.model not in models:
        ap.error(f"model '{args.model}' not in configs/models.json")
    model_cfg = models[args.model]

    specs = load_specs(args.buckets)
    if args.limit:
        specs = specs[: args.limit]
    logger.info("baseline model=%s track=%s buckets=%s specs=%d",
                args.model, args.track, args.buckets, len(specs))

    out_path = Path(args.out) if args.out else (
        outputs_dir() / f"run_{args.model}__{args.provider}_{args.track}.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)

    records, t0 = [], time.time()
    for i, spec in enumerate(specs, 1):
        rec = run_one(spec, args.track, args.provider, model_cfg)
        records.append(rec)
        if i % 10 == 0 or i == len(specs):
            from collections import Counter
            gold = [r for r in records if r["tlc_status"] == "ran"]
            sany = sum(r["syntactic_pass"] for r in records)
            tlc = sum(bool(r["tlc_pass"]) for r in gold)
            logger.info("[%d/%d] SANY %d/%d | TLC %d/%d(gold) | errs=%s",
                        i, len(specs), sany, len(records), tlc, len(gold),
                        Counter(r["error"] for r in records if r["error"]))
        # incremental save so a crash doesn't lose progress
        out_path.write_text(json.dumps(records, indent=2), encoding="utf-8")

    sany = sum(r["syntactic_pass"] for r in records)
    gold = [r for r in records if r["tlc_status"] == "ran"]
    tlc = sum(bool(r["tlc_pass"]) for r in gold)
    print(f"\nDONE model={args.model} track={args.track} n={len(records)} ({time.time()-t0:.0f}s)")
    print(f"  SANY pass (all): {sany}/{len(records)} = {sany/len(records):.1%}")
    if gold:
        print(f"  TLC pass@1 (gold subset): {tlc}/{len(gold)} = {tlc/len(gold):.1%}")
    print(f"  -> {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
