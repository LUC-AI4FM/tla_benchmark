#!/usr/bin/env python3
"""Generate the missing Claude intent descriptions with claude-opus-4-5.

Matches the original intent_claude set (same model, paper's intent prompt).
Writes descriptions/intent_claude/<id>.txt. Resumable (skips existing files).

Usage:
  python scripts/gen_claude_intent.py --smoke 2
  python scripts/gen_claude_intent.py --run --workers 6
"""
from __future__ import annotations
import argparse, json, glob, os
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "dataset_release/manifest.jsonl"
OUT_DIR = ROOT / "dataset_release/descriptions/intent_claude"
MODEL = "claude-opus-4-5"
MAX_INPUT_CHARS = 32000
MAX_OUTPUT_TOKENS = 800

PROMPT = (
    "You are writing a specification request, the way a person would describe a system "
    "they want formally specified in TLA+. You are shown an existing TLA+ module, but "
    "your task is not to describe that code. Recover the underlying intent and state it "
    "as a from-scratch request. State what system or algorithm should be modeled, what "
    "it must do, and the key correctness properties it must guarantee. Describe the goal "
    "and the requirements, not the implementation. Do not name the module's variables, "
    "operators or PlusCal structure, and do not walk through the actions step by step."
)


def load_rows():
    return [json.loads(l) for l in open(MANIFEST) if l.strip()]


def spec_path(sid):
    for tier in ("gold", "silver"):
        g = glob.glob(str(ROOT / f"dataset_release/specs/{tier}/{sid}_*.tla"))
        if g:
            return g[0]
    return None


def user_content(p):
    txt = open(p, errors="replace").read()
    if len(txt) > MAX_INPUT_CHARS:
        txt = txt[:MAX_INPUT_CHARS] + "\n... [truncated]"
    return f"{PROMPT}\n\nTLA+ module:\n{txt}"


def _one(client, sid, p):
    r = client.messages.create(
        model=MODEL, max_tokens=MAX_OUTPUT_TOKENS,
        messages=[{"role": "user", "content": user_content(p)}],
    )
    return sid, (r.content[0].text if r.content else "").strip()


def targets(rows):
    out = []
    for r in rows:
        sid = r["spec_id"]
        if (OUT_DIR / f"{sid}.txt").exists():
            continue
        p = spec_path(sid)
        if p:
            out.append((sid, p))
    return out


def run(workers):
    import anthropic
    client = anthropic.Anthropic()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    rows = load_rows()
    todo = targets(rows)
    print(f"generating {len(todo)} intent_claude descriptions with {MODEL}")
    done = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futs = {ex.submit(_one, client, sid, p): sid for sid, p in todo}
        for fut in as_completed(futs):
            sid = futs[fut]
            try:
                sid, text = fut.result()
            except Exception as e:
                print(f"  spec {sid} ERROR: {str(e)[:100]}"); continue
            if not text:
                print(f"  spec {sid} empty, skipped"); continue
            (OUT_DIR / f"{sid}.txt").write_text(text)
            done += 1
            if done % 50 == 0:
                print(f"  {done}/{len(todo)} done")
    print(f"DONE: wrote {done} intent_claude descriptions")


def smoke(n):
    import anthropic
    client = anthropic.Anthropic()
    rows = load_rows()
    for sid, p in targets(rows)[:n]:
        _, text = _one(client, sid, p)
        print(f"\n===== spec {sid} =====\n{text[:1000]}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", action="store_true")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--smoke", type=int, default=0)
    a = ap.parse_args()
    if a.smoke:
        smoke(a.smoke)
    elif a.run:
        run(a.workers)
    else:
        ap.print_help()
