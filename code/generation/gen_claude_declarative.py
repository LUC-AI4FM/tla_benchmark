#!/usr/bin/env python3
"""Generate the missing Claude declarative descriptions with claude-opus-4-5.

Matches the original declarative_claude set (same model, same prompt from the paper).
Writes descriptions/declarative_claude/<id>.txt. Resumable (skips existing files).

Usage:
  python scripts/gen_claude_declarative.py --smoke 2
  python scripts/gen_claude_declarative.py --run --workers 6
  python scripts/gen_claude_declarative.py --run --gold-only     # only the 403 gold
"""
from __future__ import annotations
import argparse, json, glob, os
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "dataset_release/manifest.jsonl"
OUT_DIR = ROOT / "dataset_release/descriptions/declarative_claude"
MODEL = "claude-opus-4-5"
MAX_INPUT_CHARS = 32000
MAX_OUTPUT_TOKENS = 800

PROMPT = (
    "You are a TLA+ specification expert. You will be given the source of a TLA+ module "
    "(and its model-checking config, if any). Write a faithful, declarative description "
    "of what the module specifies. Cover, when present, the system or algorithm being "
    "modeled, the CONSTANTS and VARIABLES, the key actions or next-state relation, the "
    "temporal specification and any fairness conditions, and the safety and liveness "
    "properties or invariants checked. Describe what the spec is and does. Do not "
    "editorialize or suggest changes. Be faithful: do not claim properties the module "
    "does not contain, and do not omit a major behavior it does contain. Write 120 to "
    "220 words in plain prose with no TLA+ code."
)


def load_rows():
    return [json.loads(l) for l in open(MANIFEST) if l.strip()]


def spec_path(sid):
    for tier in ("gold", "silver"):
        g = glob.glob(str(ROOT / f"dataset_release/specs/{tier}/{sid}_*.tla"))
        if g:
            # also append its .cfg if present (prompt says "and its config, if any")
            return g[0]
    return None


def user_content(sid, spec_path_):
    txt = open(spec_path_, errors="replace").read()
    cfg = spec_path_[:-4] + ".cfg"
    cfg_text = ""
    if os.path.exists(cfg):
        cfg_text = "\n\nConfig:\n" + open(cfg, errors="replace").read()[:4000]
    body = (txt + cfg_text)
    if len(body) > MAX_INPUT_CHARS:
        body = body[:MAX_INPUT_CHARS] + "\n... [truncated]"
    return f"{PROMPT}\n\nTLA+ module:\n{body}"


def _one(client, sid, p):
    r = client.messages.create(
        model=MODEL, max_tokens=MAX_OUTPUT_TOKENS,
        messages=[{"role": "user", "content": user_content(sid, p)}],
    )
    return sid, (r.content[0].text if r.content else "").strip()


def targets(rows, gold_only):
    out = []
    for r in rows:
        sid = r["spec_id"]
        if gold_only and r["tier"] != "gold":
            continue
        if (OUT_DIR / f"{sid}.txt").exists():
            continue
        p = spec_path(sid)
        if p:
            out.append((sid, p))
    return out


def run(workers, gold_only):
    import anthropic
    client = anthropic.Anthropic()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    rows = load_rows()
    todo = targets(rows, gold_only)
    print(f"generating {len(todo)} declarative_claude descriptions with {MODEL}"
          f"{' (gold only)' if gold_only else ''}")
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
    print(f"DONE: wrote {done} declarative_claude descriptions")


def smoke(n):
    import anthropic
    client = anthropic.Anthropic()
    rows = load_rows()
    for sid, p in targets(rows, False)[:n]:
        _, text = _one(client, sid, p)
        print(f"\n===== spec {sid} =====\n{text[:1000]}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", action="store_true")
    ap.add_argument("--gold-only", action="store_true")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--smoke", type=int, default=0)
    a = ap.parse_args()
    if a.smoke:
        smoke(a.smoke)
    elif a.run:
        run(a.workers, a.gold_only)
    else:
        ap.print_help()
