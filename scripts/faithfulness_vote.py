#!/usr/bin/env python3
"""Cross-model description-faithfulness vote.

For each spec we have two INDEPENDENT descriptions (e.g. GPT and Claude) of the
same TLA+ module, in a given style (declarative or intent). Three local models
judge whether the two descriptions AGREE on substance -- same system, same key
behaviors, same properties -- ignoring wording. Agreement across independent
descriptions is evidence the description is faithful; disagreement flags a spec
for human review.

Reuses the local-model voting pattern from classify_specs.py. Free / local.

  python scripts/faithfulness_vote.py --track declarative --bucket gold_system
  python scripts/faithfulness_vote.py --track intent --bucket gold_system

Description sources per track:
  declarative: A = GPT original (index.json 'specification'),  B = desc_claude/<sid>.txt
  intent:      A = desc_gpt_intent/<sid>.txt,                  B = desc_intent/<sid>.txt

Output: data/dataset_manifest/faithfulness_<track>/<model>.jsonl  + summary.json
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))
from utils import get_logger, load_json  # noqa: E402

logger = get_logger("faithfulness")
MDIR = REPO_ROOT / "data" / "dataset_manifest"

MODELS = ["llama3.3:70b", "qwen2.5-coder:32b", "gpt-oss:120b"]

PROMPT = """You are checking whether two independent natural-language descriptions \
describe the SAME TLA+ specification. They were written separately and will use \
different wording -- that is fine. Judge whether they AGREE ON SUBSTANCE: the \
system/algorithm being modeled, its key behaviors, and its main properties / \
invariants.

Description A:
{a}

Description B:
{b}

Reply with ONLY a JSON object, no other text:
{{"verdict": "agree" or "disagree", "conflict": "<the specific factual contradiction, or 'none'>"}}
- "agree": same system, no substantive contradiction (extra detail or different wording is OK).
- "disagree": they describe different systems, or one asserts something the other \
contradicts on substance (a real conflict, not just extra detail)."""

_THINK = re.compile(r"<think>.*?</think>", re.DOTALL)
_JSON = re.compile(r"\{[^{}]*\"verdict\"[^{}]*\}", re.DOTALL)


def desc_pair(sid: int, track: str, gpt_index: dict) -> tuple[str, str] | None:
    """Return (descA, descB) for the spec/track, or None if either is missing."""
    if track == "declarative":
        a = (gpt_index.get(sid, {}) or {}).get("specification", "")
        b_path = MDIR / "desc_claude" / f"{sid}.txt"
    else:  # intent
        a_path = MDIR / "desc_gpt_intent" / f"{sid}.txt"
        a = a_path.read_text(encoding="utf-8") if a_path.exists() else ""
        b_path = MDIR / "desc_intent" / f"{sid}.txt"
    b = b_path.read_text(encoding="utf-8") if b_path.exists() else ""
    if not a or not b:
        return None
    return a.strip(), b.strip()


def judge(client, model: str, a: str, b: str) -> dict:
    resp = client.chat.completions.create(
        model=model, max_tokens=2048, temperature=0,
        messages=[{"role": "user", "content": PROMPT.format(a=a, b=b)}])
    raw = resp.choices[0].message.content or ""
    txt = _THINK.sub("", raw).strip()
    m = _JSON.search(txt)
    if not m:
        return {"verdict": "unparsed", "conflict": txt[:80]}
    try:
        o = json.loads(m.group(0))
        v = str(o.get("verdict", "")).lower()
        return {"verdict": v if v in ("agree", "disagree") else "unparsed",
                "conflict": str(o.get("conflict", ""))[:160]}
    except json.JSONDecodeError:
        return {"verdict": "unparsed", "conflict": txt[:80]}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--track", required=True, choices=["declarative", "intent"])
    ap.add_argument("--bucket", default="gold_system")
    ap.add_argument("--models", nargs="+", default=MODELS)
    ap.add_argument("--base-url", default="http://localhost:11434/v1")
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    import openai
    client = openai.OpenAI(base_url=args.base_url, api_key="ollama")
    gpt_index = {int(k): v for k, v in load_json(REPO_ROOT / "data" / "index.json").items()}
    specs = load_json(MDIR / f"{args.bucket}.json")
    if args.limit:
        specs = specs[: args.limit]

    # which specs actually have both descriptions for this track
    pairs = {}
    for r in specs:
        p = desc_pair(r["spec_id"], args.track, gpt_index)
        if p:
            pairs[r["spec_id"]] = p
    logger.info("track=%s bucket=%s: %d/%d specs have both descriptions",
                args.track, args.bucket, len(pairs), len(specs))

    out_dir = MDIR / f"faithfulness_{args.track}"
    out_dir.mkdir(exist_ok=True)
    per_model: dict[str, dict] = {}
    for model in args.models:
        tag = re.sub(r"[^a-z0-9]", "", model.lower())
        rows = {}
        with (out_dir / f"{tag}.jsonl").open("w", encoding="utf-8") as fh:
            for i, (sid, (a, b)) in enumerate(pairs.items(), 1):
                try:
                    res = judge(client, model, a, b)
                except Exception as exc:  # noqa: BLE001
                    logger.error("model=%s sid=%s: %s", model, sid, exc)
                    res = {"verdict": "error", "conflict": str(exc)[:80]}
                row = {"spec_id": sid, "model": model, **res}
                rows[sid] = res["verdict"]
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
                fh.flush()
                if i % 25 == 0 or i == len(pairs):
                    logger.info("[%s %d/%d] %s", model, i, len(pairs),
                                dict(Counter(rows.values())))
        per_model[model] = rows

    # aggregate vote
    summary = {"track": args.track, "bucket": args.bucket, "n": len(pairs),
               "models": args.models, "by_model": {}}
    for m, rows in per_model.items():
        summary["by_model"][m] = dict(Counter(rows.values()))
    agree = disagree = contested = 0
    detail = []
    for sid in pairs:
        verdicts = [per_model[m].get(sid) for m in args.models]
        c = Counter(v for v in verdicts if v in ("agree", "disagree"))
        if not c:
            continue
        maj, n = c.most_common(1)[0]
        if maj == "agree":
            agree += 1
        else:
            disagree += 1
        if len(c) > 1:
            contested += 1
        detail.append({"spec_id": sid, "verdicts": verdicts, "majority": maj,
                       "unanimous": len(set(verdicts)) == 1})
    summary.update({"faithful_agree": agree, "disagree": disagree,
                    "contested_2_1": contested})
    (out_dir / "votes.json").write_text(json.dumps(detail, indent=2), encoding="utf-8")
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps(summary, indent=2))
    print(f"\nFlagged for review (disagree majority): {disagree}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
