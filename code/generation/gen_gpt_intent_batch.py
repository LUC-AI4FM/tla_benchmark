#!/usr/bin/env python3
"""Generate the missing GPT intent-style descriptions via the OpenAI Batch API.

Fills desc_intent for the specs that lack it, using gpt-5 (base) at batch pricing.
Reads each spec .tla, caps the input, applies the paper's intent prompt, submits one
batch, polls to completion, then writes descriptions/intent/<id>.txt and updates the
manifest.

Usage:
  python scripts/gen_gpt_intent_batch.py --build      # build the batch JSONL
  python scripts/gen_gpt_intent_batch.py --submit     # submit + poll + write results
  python scripts/gen_gpt_intent_batch.py --smoke 3    # tiny standard-API test, no batch
"""
from __future__ import annotations
import argparse, json, os, glob, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "dataset_release/manifest.jsonl"
INTENT_DIR = ROOT / "dataset_release/descriptions/intent_gpt"
BATCH_INPUT = ROOT / "outputs/gpt_intent_batch_input.jsonl"
BATCH_MAP = ROOT / "outputs/gpt_intent_batch_map.json"
MODEL = "gpt-5-mini"
REASONING = "minimal"     # keeps output/cost low; intent descs don't need deep reasoning
MAX_INPUT_CHARS = 32000   # ~8k tokens; caps the giant specs
MAX_OUTPUT_TOKENS = 2000  # minimal reasoning -> ~1000 completion tokens

PROMPT = (
    "You are writing a specification request, the way a person would describe a system "
    "they want formally specified in TLA+. You are shown an existing TLA+ module, but "
    "your task is not to describe that code. Recover the underlying intent and state it "
    "as a from-scratch request. State what system or algorithm should be modeled, what "
    "it must do, and the key correctness properties it must guarantee. Describe the goal "
    "and the requirements, not the implementation. Do not name the module's variables, "
    "operators or PlusCal structure, and do not walk through the actions step by step. "
    "Begin directly with an imperative instruction such as \"Specify ...\" or "
    "\"Model ...\". Do not use first person and do not add a title or preamble. Write 120 "
    "to 260 words of plain prose."
)


def load_rows():
    return [json.loads(l) for l in open(MANIFEST) if l.strip()]


def spec_path(spec_id):
    for tier in ("gold", "silver"):
        g = glob.glob(str(ROOT / f"dataset_release/specs/{tier}/{spec_id}_*.tla"))
        if g:
            return g[0]
    return None


def missing_specs(rows):
    out = []
    for r in rows:
        if r.get("desc_intent"):
            continue
        p = spec_path(r["spec_id"])
        if p:
            out.append((r["spec_id"], p))
    return out


def user_content(spec_text):
    if len(spec_text) > MAX_INPUT_CHARS:
        spec_text = spec_text[:MAX_INPUT_CHARS] + "\n... [truncated]"
    return f"{PROMPT}\n\nTLA+ module:\n{spec_text}"


def build():
    rows = load_rows()
    specs = missing_specs(rows)
    BATCH_INPUT.parent.mkdir(parents=True, exist_ok=True)
    with open(BATCH_INPUT, "w") as f:
        for sid, p in specs:
            txt = open(p, errors="replace").read()
            req = {
                "custom_id": f"intent-{sid}",
                "method": "POST",
                "url": "/v1/chat/completions",
                "body": {
                    "model": MODEL,
                    "messages": [{"role": "user", "content": user_content(txt)}],
                    "max_completion_tokens": MAX_OUTPUT_TOKENS,
                },
            }
            f.write(json.dumps(req) + "\n")
    print(f"built {len(specs)} requests -> {BATCH_INPUT}")


def submit():
    from openai import OpenAI
    client = OpenAI()
    up = client.files.create(file=open(BATCH_INPUT, "rb"), purpose="batch")
    batch = client.batches.create(
        input_file_id=up.id,
        endpoint="/v1/chat/completions",
        completion_window="24h",
    )
    print(f"submitted batch {batch.id}; status={batch.status}")
    while True:
        b = client.batches.retrieve(batch.id)
        print(f"  status={b.status} completed={b.request_counts.completed}/{b.request_counts.total}")
        if b.status in ("completed", "failed", "expired", "cancelled"):
            break
        time.sleep(30)
    if b.status != "completed":
        print(f"batch ended: {b.status}"); return
    out = client.files.content(b.output_file_id).text
    INTENT_DIR.mkdir(parents=True, exist_ok=True)
    rows = load_rows()
    by_id = {r["spec_id"]: r for r in rows}
    written = 0
    for line in out.splitlines():
        if not line.strip():
            continue
        rec = json.loads(line)
        sid = int(rec["custom_id"].split("-")[1])
        body = rec.get("response", {}).get("body", {})
        try:
            text = body["choices"][0]["message"]["content"].strip()
        except Exception:
            continue
        if not text:
            continue
        (INTENT_DIR / f"{sid}.txt").write_text(text)
        if sid in by_id:
            by_id[sid]["desc_intent"] = text
        written += 1
    with open(MANIFEST, "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    print(f"wrote {written} intent descriptions + updated manifest")


def _one(client, sid, p):
    txt = open(p, errors="replace").read()
    r = client.chat.completions.create(
        model=MODEL,
        messages=[{"role": "user", "content": user_content(txt)}],
        max_completion_tokens=MAX_OUTPUT_TOKENS,
        reasoning_effort=REASONING,
    )
    return sid, (r.choices[0].message.content or "").strip()


def run(workers=8):
    """Standard parallel generation (instant, resumable). Writes files + manifest."""
    from openai import OpenAI
    from concurrent.futures import ThreadPoolExecutor, as_completed
    client = OpenAI()
    INTENT_DIR.mkdir(parents=True, exist_ok=True)
    rows = load_rows()
    by_id = {r["spec_id"]: r for r in rows}
    # Generate a GPT intent description for every spec that has a spec file but no
    # intent_gpt/<id>.txt yet (resumable). Independent of the manifest desc_intent field.
    todo = []
    for r in rows:
        sid = r["spec_id"]
        if (INTENT_DIR / f"{sid}.txt").exists():
            continue
        p = spec_path(sid)
        if p:
            todo.append((sid, p))
    print(f"generating {len(todo)} intent descriptions with {MODEL} ({REASONING} reasoning)")
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
            (INTENT_DIR / f"{sid}.txt").write_text(text)
            done += 1
            if done % 50 == 0:
                print(f"  {done}/{len(todo)} done")
    print(f"DONE: wrote {done} GPT intent descriptions to {INTENT_DIR.name}/")


def smoke(n):
    from openai import OpenAI
    client = OpenAI()
    rows = load_rows()
    specs = missing_specs(rows)[:n]
    for sid, p in specs:
        _, text = _one(client, sid, p)
        print(f"\n===== spec {sid} =====")
        print(text[:1200])


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--submit", action="store_true")
    ap.add_argument("--run", action="store_true", help="standard parallel generation (instant)")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--smoke", type=int, default=0)
    a = ap.parse_args()
    if a.smoke:
        smoke(a.smoke)
    elif a.run:
        run(a.workers)
    elif a.build:
        build()
    elif a.submit:
        submit()
    else:
        ap.print_help()
