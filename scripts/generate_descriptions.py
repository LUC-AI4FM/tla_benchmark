#!/usr/bin/env python3
"""Generate a second, independent description per spec with Claude (Sonnet 4.6).

Reads the verified .tla (+ .cfg if present) and writes a faithful, declarative
description in the same style as the existing GPT descriptions. These second
descriptions feed the cross-model faithfulness check (Claude vs GPT, voted by
local models) -- see scripts/classify_specs.py for the voting pattern.

Uses the official Anthropic SDK. The shared system prompt is prompt-cached so
only the per-spec .tla/.cfg is billed at full input price. Sonnet 4.6,
thinking off (a description is a read->write task, no reasoning needed).

  export ANTHROPIC_API_KEY=sk-ant-...
  python scripts/generate_descriptions.py --buckets gold_system --dry-run
  python scripts/generate_descriptions.py --buckets gold_system --limit 5
  python scripts/generate_descriptions.py --buckets gold_system silver

Output: data/dataset_manifest/desc_claude/<spec_id>.txt  + index.jsonl
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))
from utils import get_logger, load_json  # noqa: E402

logger = get_logger("gen_desc")

MODEL = "claude-sonnet-4-6"
PRICE_IN, PRICE_OUT = 3.0, 15.0  # $/1M tokens (Sonnet 4.6)

SYSTEM_DECLARATIVE = """You are a TLA+ specification expert. You will be given \
the source of a TLA+ module (and its model-checking config, if any). Write a \
faithful, declarative description of what the module specifies.

Cover, when present: the system or algorithm being modeled, the CONSTANTS and \
VARIABLES, the key actions / next-state relation, the temporal specification and \
any fairness conditions, and the safety/liveness properties or invariants checked.

Rules:
- Describe what the spec IS and DOES -- do not editorialize, critique, or suggest.
- Be faithful: do not claim properties the module does not contain, and do not \
omit a major behavior it does contain.
- If the module is a utility, test, or model-checking wrapper rather than a real \
system, say so plainly.
- 120-220 words, one or two paragraphs. Plain prose, no bullet lists.
- Do NOT include any TLA+ code, and do not start with "This description".
"""

SYSTEM_INTENT = """You are writing a SPECIFICATION REQUEST -- a brief, the way a \
person would describe a system they want formally specified in TLA+. You will be \
shown an existing TLA+ module, but your job is NOT to describe that code; it is to \
recover the underlying intent and state it as a from-scratch request.

State: what system or algorithm should be modeled, what it must do, and the key \
correctness properties it must guarantee (the safety and liveness requirements).

Rules:
- Describe the GOAL and REQUIREMENTS, not the implementation. Do NOT name the \
module's variables, operators, or PlusCal structure, and do NOT walk through the \
actions step by step. Someone reading your brief should have to DESIGN the spec, \
not transcribe it.
- DO include the essential behaviors and the properties that must hold -- a correct \
spec will be checked against these, so they must be faithful: every property you \
state must actually hold in the module, and don't invent requirements it lacks.
- If the module is a utility/test/demonstration rather than a real system, frame \
the request accordingly (e.g. "Write a small module that demonstrates ...").
- Phrase it as a request: start with "Specify ..." or "Write a TLA+ specification \
for ...". 100-180 words, plain prose, no bullet lists, no TLA+ code.
"""

PROMPTS = {"declarative": SYSTEM_DECLARATIVE, "intent": SYSTEM_INTENT}
# output dir per (provider, style) -- keeps each model's descriptions separate
OUT_DIRS = {
    ("anthropic", "declarative"): "desc_claude",
    ("anthropic", "intent"): "desc_intent",
    ("openai", "declarative"): "desc_gpt",
    ("openai", "intent"): "desc_gpt_intent",
}
DEFAULT_MODEL = {"anthropic": "claude-sonnet-4-6", "openai": "gpt-5.5"}
# $/1M tokens (in, out). openai gpt-5.5 left None -> cost reported as token counts only.
PRICE = {"claude-sonnet-4-6": (3.0, 15.0)}


def call_openai(client, model, system_text, user_text, max_tokens):
    """OpenAI chat completion; tolerates reasoning-model temperature restriction."""
    kwargs = {"model": model, "max_completion_tokens": max_tokens,
              "messages": [{"role": "system", "content": system_text},
                           {"role": "user", "content": user_text}]}
    try:
        r = client.chat.completions.create(**kwargs)
    except Exception as exc:  # reasoning models reject temperature; default is fine
        raise exc
    c = r.choices[0]
    u = r.usage
    return (c.message.content or "",
            u.prompt_tokens if u else 0, u.completion_tokens if u else 0, 0)


def find_cfg(tla: Path) -> Path | None:
    same = tla.with_suffix(".cfg")
    if same.exists():
        return same
    cfgs = list(tla.parent.glob("*.cfg"))
    return cfgs[0] if len(cfgs) == 1 else None


def build_user_content(tla: Path) -> str:
    parts = [f"=== MODULE {tla.stem} ({tla.name}) ===\n",
             tla.read_text(encoding="utf-8", errors="replace")]
    cfg = find_cfg(tla)
    if cfg is not None:
        parts.append(f"\n\n=== CONFIG ({cfg.name}) ===\n")
        parts.append(cfg.read_text(encoding="utf-8", errors="replace"))
    return "".join(parts)


def load_specs(buckets: list[str]) -> list[dict]:
    mdir = REPO_ROOT / "data" / "dataset_manifest"
    seen, out = set(), []
    for b in buckets:
        for r in load_json(mdir / f"{b}.json"):
            if r["spec_id"] not in seen:
                seen.add(r["spec_id"])
                out.append(r)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--buckets", nargs="+", default=["gold_system"],
                    help="manifest buckets to describe (e.g. gold_system silver)")
    ap.add_argument("--style", nargs="+", default=["declarative"],
                    choices=["declarative", "intent"],
                    help="declarative (translation) and/or intent (design) descriptions")
    ap.add_argument("--provider", default="anthropic", choices=["anthropic", "openai"])
    ap.add_argument("--model", default=None, help="defaults per provider")
    ap.add_argument("--max-tokens", type=int, default=1024)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--dry-run", action="store_true",
                    help="count specs + estimate cost, no API calls")
    args = ap.parse_args()
    if args.model is None:
        args.model = DEFAULT_MODEL[args.provider]
    p_in, p_out = PRICE.get(args.model, (0.0, 0.0))

    specs = load_specs(args.buckets)
    if args.limit:
        specs = specs[: args.limit]
    n_calls = len(specs) * len(args.style)
    logger.info("describing %d specs x styles=%s from %s with %s (%d calls)",
                len(specs), args.style, args.buckets, args.model, n_calls)

    if args.dry_run:
        in_tok = len(args.style) * sum(
            len(build_user_content(REPO_ROOT / r["tla_path"])) // 4 + 400 for r in specs)
        out_tok = n_calls * 350
        cost = in_tok / 1e6 * p_in + out_tok / 1e6 * p_out
        print(f"provider={args.provider} model={args.model} specs={len(specs)} "
              f"styles={args.style} calls={n_calls}")
        print(f"est_input_tok~{in_tok:,}  est_output_tok~{out_tok:,}")
        if p_in:
            print(f"est cost (sync) ~ ${cost:.2f}  (Batch ~${cost/2:.2f})")
        else:
            print("(no price table for this model -- token counts reported, cost unknown)")
        return 0

    if args.provider == "anthropic":
        import anthropic
        client = anthropic.Anthropic()
    else:
        import openai
        client = openai.OpenAI()
    tot_in = tot_out = tot_cached = done = 0

    for style in args.style:
        out_dir = REPO_ROOT / "data" / "dataset_manifest" / OUT_DIRS[(args.provider, style)]
        out_dir.mkdir(exist_ok=True)
        logger.info("== provider=%s style=%s -> %s ==", args.provider, style, out_dir.name)
        with (out_dir / "index.jsonl").open("a", encoding="utf-8") as fh:
            for i, r in enumerate(specs, 1):
                sid = r["spec_id"]
                tla = REPO_ROOT / r["tla_path"]
                user_text = build_user_content(tla)
                try:
                    if args.provider == "anthropic":
                        system = [{"type": "text", "text": PROMPTS[style],
                                   "cache_control": {"type": "ephemeral"}}]
                        resp = client.messages.create(
                            model=args.model, max_tokens=args.max_tokens, system=system,
                            messages=[{"role": "user", "content": user_text}])
                        text = next((b.text for b in resp.content if b.type == "text"), "").strip()
                        ti, to = resp.usage.input_tokens, resp.usage.output_tokens
                        tot_cached += getattr(resp.usage, "cache_read_input_tokens", 0) or 0
                    else:
                        text, ti, to, _ = call_openai(
                            client, args.model, PROMPTS[style], user_text, args.max_tokens)
                        text = text.strip()
                except Exception as exc:  # noqa: BLE001
                    logger.error("sid=%s style=%s failed: %s", sid, style, exc)
                    time.sleep(2)
                    continue
                (out_dir / f"{sid}.txt").write_text(text, encoding="utf-8")
                tot_in += ti
                tot_out += to
                fh.write(json.dumps({"spec_id": sid, "name": tla.name, "style": style,
                                     "provider": args.provider, "model": args.model,
                                     "tokens_in": ti, "tokens_out": to,
                                     "words": len(text.split())}, ensure_ascii=False) + "\n")
                fh.flush()
                done += 1
                if i % 10 == 0 or i == len(specs):
                    cost = tot_in / 1e6 * p_in + tot_out / 1e6 * p_out
                    logger.info("[%s %d/%d] done=%d in=%d out=%d ~$%.2f%s",
                                style, i, len(specs), done, tot_in, tot_out, cost,
                                "" if p_in else " (price n/a)")

    cost = tot_in / 1e6 * p_in + tot_out / 1e6 * p_out
    print(f"\nDONE: {done}/{n_calls} descriptions ({args.provider} {args.style})")
    print(f"tokens in={tot_in:,} (cached {tot_cached:,}) out={tot_out:,} | "
          f"cost ~${cost:.2f}" if p_in else
          f"tokens in={tot_in:,} out={tot_out:,} | (price n/a for {args.model})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
