#!/usr/bin/env python3
"""Label each spec's DESCRIPTION as 'system' vs 'utility' with a local model.

system  = models a real system/algorithm/protocol with behaviour (state,
          actions, concurrency, data structure with operations, ...).
utility = test fixture, feature/syntax demo, model-checking wrapper, constant/
          operator-only helper, thin instance/annotation wrapper.

Reads from a manifest bucket (default gold), classifies via an Ollama model,
writes <out> with {spec_id, label, reason, name}. Free / local.

  python scripts/classify_specs.py --model llama3.3:70b --bucket gold
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))
from utils import get_logger, load_json  # noqa: E402

logger = get_logger("classify_specs")

PROMPT = """You classify descriptions of TLA+ specifications.

Decide one label:
- "system": the module models a real system, algorithm, or protocol with actual
  behaviour - state variables that change, actions/next-state relations,
  concurrency or distribution, a data structure with operations, a temporal
  spec of how something evolves.
- "utility": the module is NOT a system. It is a test fixture, a regression or
  feature/syntax demonstration, a model-checking wrapper/config helper, a module
  that only defines constants/operators/expressions, or a thin INSTANCE/type
  annotation wrapper that adds no behaviour of its own.

Reply with ONLY a JSON object, no other text:
{{"label": "system" or "utility", "reason": "<short phrase>"}}

Description:
{desc}
"""

_THINK = re.compile(r"<think>.*?</think>", re.DOTALL)
_JSON = re.compile(r"\{[^{}]*\"label\"[^{}]*\}", re.DOTALL)


def classify(client, model: str, desc: str) -> dict:
    resp = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": PROMPT.format(desc=desc)}],
        max_tokens=4096, temperature=0)
    raw = resp.choices[0].message.content or ""
    txt = _THINK.sub("", raw).strip()
    m = _JSON.search(txt)
    if not m:
        return {"label": "unparsed", "reason": txt[:80]}
    try:
        obj = json.loads(m.group(0))
        label = str(obj.get("label", "")).lower()
        return {"label": label if label in ("system", "utility") else "unparsed",
                "reason": str(obj.get("reason", ""))[:120]}
    except json.JSONDecodeError:
        return {"label": "unparsed", "reason": txt[:80]}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="llama3.3:70b")
    ap.add_argument("--base-url", default="http://localhost:11434/v1")
    ap.add_argument("--bucket", default="gold", help="manifest bucket to classify")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    import openai
    client = openai.OpenAI(base_url=args.base_url, api_key="ollama")

    mdir = REPO_ROOT / "data" / "dataset_manifest"
    specs = load_json(mdir / f"{args.bucket}.json")
    idx = {int(k): v for k, v in load_json(REPO_ROOT / "data" / "index.json").items()}
    if args.limit:
        specs = specs[: args.limit]
    out_path = Path(args.out) if args.out else mdir / f"class_{args.bucket}.jsonl"
    logger.info("classifying %d specs from %s with %s", len(specs), args.bucket, args.model)

    rows = []
    with out_path.open("w", encoding="utf-8") as fh:
        for i, r in enumerate(specs, 1):
            sid = r["spec_id"]
            desc = idx[sid].get("specification", "")
            res = classify(client, args.model, desc)
            row = {"spec_id": sid, "name": Path(r["tla_path"]).name,
                   "tier": r.get("complexity_tier"), **res}
            rows.append(row)
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")
            fh.flush()
            if i % 25 == 0 or i == len(specs):
                from collections import Counter
                logger.info("[%d/%d] %s", i, len(specs),
                            dict(Counter(x["label"] for x in rows)))

    from collections import Counter
    counts = Counter(x["label"] for x in rows)
    print(json.dumps({"model": args.model, "bucket": args.bucket, "n": len(rows),
                      "labels": dict(counts), "out": str(out_path)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
