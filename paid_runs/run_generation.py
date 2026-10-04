#!/usr/bin/env python3
"""Generate TLA+ specifications for the 100 evaluation items and grade them with SANY and TLC.

One runner for every paid job in jobs.sh. Each job is a combination of
  provider     bedrock | anthropic | openai | google | ollama
  mode         default (description only) | cfgaware (description + the cfg's names)
  description  gpt | claude (which provider wrote the declarative description)
  samples      how many independent generations per specification

Results go to results/<label>__<mode>__<desc>desc/ :
  results.json             one graded record per (specification, sample)
  generations/<id>_s<k>.tla
The runner resumes: finished (specification, sample) pairs are skipped. A failed API call is
never saved, so re-running the same command retries it. Nothing is written for a failed call.

No API keys are stored here. Credentials come from the environment:
  bedrock    the standard AWS credential chain (aws configure, AWS_PROFILE, instance role)
  anthropic  ANTHROPIC_API_KEY
  openai     OPENAI_API_KEY
  google     GEMINI_API_KEY
"""
from __future__ import annotations
import argparse, json, os, sys, threading, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

HERE = Path(__file__).resolve().parent      # paid_runs/: prompts and results
ROOT = HERE.parent                           # repository root: specs, manifest, descriptions, grader
sys.path.insert(0, str(ROOT / "code" / "analysis"))
import grading as G  # noqa: E402  (SANY + TLC grader, identical to the released one)

# USD per 1M input / output tokens, used only for the --cap safety stop
PRICE = {"bedrock": (5.0, 25.0), "anthropic": (5.0, 25.0), "openai": (1.25, 10.0),
         "google": (1.25, 10.0), "ollama": (0.0, 0.0)}


class Stop(Exception):
    """Spend cap or provider daily limit reached: stop the whole run."""


class Failed(Exception):
    """One request failed after retries: leave this item undone."""


def make_call(a):
    """Return call(prompt) -> (text, finish_reason, tokens_in, tokens_out)."""
    if a.provider == "bedrock":
        import boto3
        from botocore.config import Config
        client = boto3.client("bedrock-runtime", region_name=a.region,
                              config=Config(read_timeout=1800, connect_timeout=60,
                                            retries={"max_attempts": 3, "mode": "adaptive"}))

        def call(prompt):
            inf = {"maxTokens": a.max_tokens}
            if a.temperature is not None:
                inf["temperature"] = a.temperature
            r = client.converse(modelId=a.model_id, inferenceConfig=inf,
                                messages=[{"role": "user", "content": [{"text": prompt}]}])
            text = "".join(c.get("text", "") for c in r["output"]["message"]["content"])
            u = r.get("usage", {})
            return text, r.get("stopReason"), u.get("inputTokens", 0), u.get("outputTokens", 0)
        return call

    if a.provider == "anthropic":
        import anthropic
        client = anthropic.Anthropic(api_key=os.environ["ANTHROPIC_API_KEY"], timeout=1800)

        def call(prompt):
            kw = {"temperature": a.temperature} if a.temperature is not None else {}
            r = client.messages.create(model=a.model_id, max_tokens=a.max_tokens,
                                       messages=[{"role": "user", "content": prompt}], **kw)
            text = "".join(b.text for b in r.content if b.type == "text")
            return text, r.stop_reason, r.usage.input_tokens, r.usage.output_tokens
        return call

    if a.provider == "openai":
        import openai
        client = openai.OpenAI(api_key=os.environ["OPENAI_API_KEY"])

        def call(prompt):
            # GPT-5 accepts only its default temperature, so none is sent
            r = client.chat.completions.create(model=a.model_id, max_completion_tokens=a.max_tokens,
                                               messages=[{"role": "user", "content": prompt}])
            return (r.choices[0].message.content or "", r.choices[0].finish_reason,
                    r.usage.prompt_tokens, r.usage.completion_tokens)
        return call

    if a.provider == "google":
        from google import genai
        from google.genai import types
        client = genai.Client(api_key=os.environ["GEMINI_API_KEY"])

        def call(prompt):
            cfg = {}
            if a.temperature is not None:
                cfg["temperature"] = a.temperature
            if a.max_tokens:
                cfg["max_output_tokens"] = a.max_tokens
            r = client.models.generate_content(model=a.model_id, contents=prompt,
                                               config=types.GenerateContentConfig(**cfg))
            um = r.usage_metadata
            out = (um.candidates_token_count or 0) + (getattr(um, "thoughts_token_count", 0) or 0)
            fr = r.candidates[0].finish_reason.name if r.candidates and r.candidates[0].finish_reason else None
            return r.text or "", fr, um.prompt_token_count or 0, out
        return call

    if a.provider == "ollama":
        import requests

        def call(prompt):
            opts = {"temperature": a.temperature if a.temperature is not None else 0.0,
                    "num_predict": a.max_tokens}
            if a.num_ctx:
                opts["num_ctx"] = a.num_ctx
            r = requests.post(f"{a.ollama_url}/api/generate", timeout=3600,
                              json={"model": a.model_id, "prompt": prompt, "stream": False, "options": opts})
            r.raise_for_status()
            b = r.json()
            return b.get("response", ""), b.get("done_reason"), b.get("prompt_eval_count", 0), b.get("eval_count", 0)
        return call
    raise SystemExit(f"unknown provider {a.provider}")


def build_prompt(a, rec, names):
    if a.desc.startswith("intent_"):   # name-hidden intent style, from descriptions/<style>/<id>.txt
        desc = (ROOT / "descriptions" / a.desc / f"{rec['spec_id']}.txt").read_text(encoding="utf-8").strip()
    else:
        desc = rec.get(f"desc_declarative_{a.desc}") or ""
    if a.mode == "cfgaware":
        return G.GEN_PROMPT_CFG.format(description=desc, names=names)
    if a.template == "open":   # the template the open models were evaluated with
        return (HERE / "prompts" / "nlp_to_tla.txt").read_text(encoding="utf-8").replace("{description}", desc)
    return G.GEN_PROMPT.format(description=desc)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--provider", required=True, choices=list(PRICE))
    ap.add_argument("--model-id", required=True, help="exact model or Bedrock inference-profile id")
    ap.add_argument("--label", required=True, help="model name used in result files, e.g. claude-opus-4-5")
    ap.add_argument("--mode", choices=["default", "cfgaware"], default="default")
    ap.add_argument("--desc", choices=["gpt", "claude", "intent_gpt", "intent_claude"], default="gpt",
                    help="declarative description (gpt, claude) or name-hidden intent description")
    ap.add_argument("--template", choices=["frontier", "open"], default="frontier",
                    help="default-mode prompt: frontier models or the open-model template")
    ap.add_argument("--samples", type=int, default=1, help="generations per specification")
    ap.add_argument("--sample-offset", type=int, default=0,
                    help="index of the first sample (e.g. 1 when sample 0 already exists)")
    ap.add_argument("--max-tokens", type=int, default=16000, help="0 = provider default (google only)")
    ap.add_argument("--temperature", type=float, default=None, help="omit to use the provider default")
    ap.add_argument("--region", default=os.environ.get("AWS_REGION", "us-east-1"))
    ap.add_argument("--ollama-url", default=os.environ.get("OLLAMA_URL", "http://localhost:11434"))
    ap.add_argument("--num-ctx", type=int, default=0, help="ollama context window (0 = default)")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--min-interval", type=float, default=0.0, help="seconds between requests (rate limits)")
    ap.add_argument("--cap", type=float, default=60.0, help="stop when estimated spend reaches this (USD)")
    ap.add_argument("--limit", type=int, default=0, help="only the first N specifications (smoke test)")
    ap.add_argument("--dry-run", action="store_true", help="print the first prompt and exit, no API call")
    a = ap.parse_args()
    if a.desc.startswith("intent_") and a.mode == "cfgaware":
        ap.error("intent descriptions hide the names; use them only in the default mode")

    man = {str(json.loads(l)["spec_id"]): json.loads(l) for l in open(ROOT / "manifest.jsonl")}
    ids = [str(s) for s in json.load(open(ROOT / "outputs" / "eval_100_ids.json"))]
    if a.limit:
        ids = ids[:a.limit]
    samples = list(range(a.sample_offset, a.sample_offset + a.samples))

    def names_for(sid):
        _, cfg = G.gold_paths(sid)
        return G.cfg_names(cfg.read_text(errors="replace")) if cfg else ""

    if a.dry_run:
        print(build_prompt(a, man[ids[0]], names_for(ids[0])))
        return 0

    out_dir = HERE / "results" / f"{a.label}__{a.mode}__{a.desc}desc"
    gen_dir = out_dir / "generations"
    gen_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / "results.json"
    rows = json.load(open(out)) if out.exists() else []
    done = {(r["spec_id"], r["sample"]) for r in rows}
    todo = [(s, k) for s in ids for k in samples if (s, k) not in done]
    print(f"{a.label} {a.mode} ({a.desc} descriptions): {len(done)} done, {len(todo)} to run", flush=True)

    call = make_call(a)
    lock, spend, pace = threading.Lock(), {"usd": 0.0}, {"next": 0.0}
    p_in, p_out = PRICE[a.provider]

    def generate(prompt):
        last = None
        for attempt in range(6):
            with lock:
                if spend["usd"] >= a.cap:
                    raise Stop(f"spend cap ${a.cap} reached")
                now = time.time(); start = max(now, pace["next"]); pace["next"] = start + a.min_interval
            time.sleep(max(0.0, start - now))
            try:
                text, finish, tin, tout = call(prompt)
                with lock:
                    spend["usd"] += (tin * p_in + tout * p_out) / 1e6
                return text, finish, tin, tout
            except Exception as e:  # noqa: BLE001
                if "requests per day" in str(e):
                    raise Stop(f"daily request limit: {str(e)[:150]}")
                last = e
                wait = min(120, 5 * 2 ** attempt)
                print(f"  retry {attempt} in {wait}s: {str(e)[:150]}", flush=True)
                time.sleep(wait)
        raise Failed(str(last)[:200])

    def work(item):
        sid, k = item
        tla, cfg = G.gold_paths(sid)
        prompt = build_prompt(a, man[sid], names_for(sid))
        text, finish, tin, tout = generate(prompt)
        gen = G.extract_module(text)
        (gen_dir / f"{sid}_s{k}.tla").write_text(gen)
        g = G.grade_clean(gen, tla)
        return {"spec_id": sid, "sample": k, "model": a.label, "model_id": a.model_id,
                "provider": a.provider, "mode": a.mode, "desc_provider": a.desc,
                "template": a.template if a.mode == "default" else "cfgaware",
                "max_tokens": a.max_tokens, "temperature": a.temperature, "finish_reason": finish,
                "tokens_in": tin, "tokens_out": tout, "empty_response": not gen.strip(), **g}

    stopped = None
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        futs = {pool.submit(work, it): it for it in todo}
        for f in as_completed(futs):
            try:
                r = f.result()
            except Stop as e:
                stopped = str(e); continue
            except Failed as e:
                print(f"  {futs[f]}: left undone ({e})", flush=True); continue
            with lock:
                rows.append(r)
                rows.sort(key=lambda x: (int(x["spec_id"]), x["sample"]))
                json.dump(rows, open(out, "w"), indent=1)
                c = sum(bool(x["tlc_pass"]) for x in rows)
                print(f"  {r['spec_id']} s{r['sample']}: sany={r['sany_pass']} tlc={r['tlc_pass']} "
                      f"finish={r['finish_reason']} | {c}/{len(rows)} correct | ~${spend['usd']:.2f}", flush=True)
    total = len(ids) * len(samples)
    print(f"=== {a.label} {a.mode} ({a.desc}): {len(rows)}/{total} graded, "
          f"{sum(bool(x['tlc_pass']) for x in rows)} correct, ~${spend['usd']:.2f} this session"
          + (f" | STOPPED: {stopped}" if stopped else ""), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
