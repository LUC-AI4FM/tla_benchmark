from __future__ import annotations

import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from checkpoint import CheckpointManager
from utils import (
    data_dir, get_logger, get_spec_by_id, load_json, load_text,
    outputs_dir, repo_root, retry_with_backoff, save_json,
)
from parser import extract_tla_from_response
from validator import validate_spec

logger = get_logger("runner")

_PROMPT_TEMPLATE_FOR = {
    "nlp_to_tla": "nlp_to_tla.txt",
    "v2_to_tla": "json_to_tla.txt",
    "v3_to_tla": "v3_to_tla.txt",
    "nlp_v2_to_tla": "nlp_v2_to_tla.txt",
    "nlp_v3_to_tla": "nlp_v3_to_tla.txt",
}

ALL_CONDITIONS = list(_PROMPT_TEMPLATE_FOR.keys())
KNOWN_TIERS = {"basic", "intermediate", "advanced", "auxiliary"}


def _call_ollama(model_name: str, prompt: str, temperature: float, max_tokens: int, host: str = "http://localhost:11434") -> dict[str, Any]:
    import requests
    resp = requests.post(
        f"{host}/api/generate",
        json={"model": model_name, "prompt": prompt, "stream": False,
              "options": {"temperature": temperature, "num_predict": max_tokens}},
        timeout=600,
    )
    resp.raise_for_status()
    data = resp.json()
    thinking = data.get("thinking", "") or ""
    response = data.get("response", "") or ""
    text = (thinking + "\n" + response).strip() if thinking else response
    return {"text": text, "tokens_in": data.get("prompt_eval_count", 0), "tokens_out": data.get("eval_count", 0)}


def _call_openai(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import openai
    client = openai.OpenAI()
    kwargs: dict[str, Any] = {
        "model": model_name,
        "messages": [{"role": "user", "content": prompt}],
        "max_completion_tokens": max_tokens,
    }
    if temperature != 1:
        kwargs["temperature"] = temperature
    response = client.chat.completions.create(**kwargs)
    choice = response.choices[0]
    return {
        "text": choice.message.content or "",
        "tokens_in": response.usage.prompt_tokens if response.usage else 0,
        "tokens_out": response.usage.completion_tokens if response.usage else 0,
    }


def _call_anthropic(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import requests
    api_key = os.environ.get("ANTHROPIC_API_KEY", "")
    if not api_key:
        raise ValueError("ANTHROPIC_API_KEY is not set")
    resp = requests.post(
        "https://api.anthropic.com/v1/messages",
        headers={"x-api-key": api_key, "anthropic-version": "2023-06-01", "content-type": "application/json"},
        json={"model": model_name, "max_tokens": max_tokens, "temperature": temperature,
              "messages": [{"role": "user", "content": prompt}]},
        timeout=600,
    )
    resp.raise_for_status()
    data = resp.json()
    return {
        "text": "".join(c.get("text", "") for c in data.get("content", [])),
        "tokens_in": data.get("usage", {}).get("input_tokens", 0),
        "tokens_out": data.get("usage", {}).get("output_tokens", 0),
    }


def _call_google(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import requests
    api_key = os.environ.get("GEMINI_API_KEY", "")
    if not api_key:
        raise ValueError("GEMINI_API_KEY is not set")
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent?key={api_key}"
    resp = requests.post(url, json={
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {"temperature": temperature, "maxOutputTokens": max_tokens},
    }, timeout=300)
    resp.raise_for_status()
    data = resp.json()
    try:
        text = data["candidates"][0]["content"]["parts"][0]["text"]
    except (KeyError, IndexError):
        text = ""
    usage = data.get("usageMetadata", {})
    return {"text": text, "tokens_in": usage.get("promptTokenCount", 0), "tokens_out": usage.get("candidatesTokenCount", 0)}


def _call_model(cfg: dict[str, Any], prompt: str) -> dict[str, Any]:
    backend = cfg["backend"]
    model_name = cfg["model_name"]
    temperature = cfg.get("temperature", 0.0)
    max_tokens = cfg.get("max_tokens", 8192)
    if backend == "ollama":
        host = cfg.get("ollama_host", "http://localhost:11434")
        return _call_ollama(model_name, prompt, temperature, max_tokens, host)
    dispatch = {"openai": _call_openai, "anthropic": _call_anthropic, "google": _call_google}
    if backend not in dispatch:
        raise ValueError(f"Unknown backend: {backend!r}")
    return dispatch[backend](model_name, prompt, temperature, max_tokens)


def _get_cfg_path(spec_id: int, module_name: str) -> str | None:
    for candidate in (
        data_dir() / "cfg" / f"{spec_id}.cfg",
        data_dir() / "cfg" / f"{module_name}.cfg",
    ):
        if candidate.exists():
            return str(candidate)
    return None


def _load_description(spec_id: int) -> str | None:
    p = data_dir() / "descriptions" / f"{spec_id}.txt"
    if p.exists():
        return p.read_text(encoding="utf-8")
    return None


_V3_ONLY_FIELDS = frozenset({
    "Specification", "_changelog",
    "OperatorDefNames_StatePredicate", "OperatorDefNames_TemporalProperty",
    "OperatorDefNames_Init", "OperatorDefNames_ValueDef",
    "FunctionConstructor_ByDomain", "FunctionConstructor_SetType",
    "UnchangedExprs_Explicit", "UnchangedExprs_VarRef",
    "TemporalNesting", "CorpusSource", "VerificationTools", "DivisionNotes",
})


def _load_parsed(spec_data: dict) -> dict | None:
    parsed_path = spec_data.get("parsed_path")
    if not parsed_path:
        return None
    p = repo_root() / parsed_path
    if not p.exists():
        return None
    return json.loads(p.read_text(encoding="utf-8"))


def _resolve_input(spec_id: int, condition: str, spec_data: dict) -> str | None:
    if condition == "nlp_to_tla":
        return _load_description(spec_id)
    if condition == "v2_to_tla":
        parsed = _load_parsed(spec_data)
        if parsed is None:
            return None
        return json.dumps({k: v for k, v in parsed.items() if k not in _V3_ONLY_FIELDS})
    if condition == "v3_to_tla":
        parsed = _load_parsed(spec_data)
        if parsed is None:
            return None
        return json.dumps(parsed)
    if condition in ("nlp_v2_to_tla", "nlp_v3_to_tla"):
        description = _load_description(spec_id)
        if description is None:
            return None
        parsed = _load_parsed(spec_data)
        if parsed is None:
            return None
        if condition == "nlp_v2_to_tla":
            json_content = {k: v for k, v in parsed.items() if k not in _V3_ONLY_FIELDS}
        else:
            json_content = parsed
        return json.dumps({"description": description, "json_content": json_content})
    return None


def _process_spec(
    spec_id: int,
    condition: str,
    spec_data: dict,
    model_cfg: dict,
    templates: dict[str, str],
) -> dict | None:
    model_id = model_cfg["id"]
    complexity_tier = spec_data.get("complexity_tier") or spec_data.get("ComplexityTier", "unknown")
    module_name = spec_data.get("module_name") or spec_data.get("ModuleName", str(spec_id))

    if complexity_tier not in KNOWN_TIERS:
        logger.warning("spec=%d: unrecognised ComplexityTier=%r", spec_id, complexity_tier)

    input_text = _resolve_input(spec_id, condition, spec_data)
    if input_text is None:
        return None

    template = templates[condition]
    if condition in ("nlp_v2_to_tla", "nlp_v3_to_tla"):
        parsed = json.loads(input_text)
        prompt_text = template.replace("{description}", parsed["description"]).replace(
            "{json_content}", json.dumps(parsed["json_content"])
        )
    elif "{description}" in template:
        prompt_text = template.replace("{description}", input_text)
    elif "{json_content}" in template:
        prompt_text = template.replace("{json_content}", input_text)
    else:
        prompt_text = template

    def _base_record(error: str) -> dict:
        return {
            "spec_id": spec_id, "model_id": model_id, "condition": condition,
            "complexity_tier": complexity_tier, "sany_pass": False,
            "tlc_pass": False, "pass_at_1": False, "error": error,
        }

    try:
        result = retry_with_backoff(lambda: _call_model(model_cfg, prompt_text))
        extracted = extract_tla_from_response(result["text"])
        if not extracted:
            logger.error("spec=%d model=%s condition=%s: extraction failed", spec_id, model_id, condition)
            return _base_record("extraction_failed")

        val_dir = outputs_dir() / "validation" / model_id / condition
        spec_val_dir = val_dir / str(spec_id)
        spec_val_dir.mkdir(parents=True, exist_ok=True)
        tla_path = spec_val_dir / f"{module_name}.tla"

        try:
            tla_path.write_text(extracted)
            cfg_path = _get_cfg_path(spec_id, module_name)
            summary = validate_spec(str(tla_path), cfg_path, str(val_dir), spec_id, model_id, condition)
            summary["complexity_tier"] = complexity_tier
            summary["pass_at_1"] = bool(summary.get("sany_pass") and summary.get("tlc_pass"))
            return summary
        finally:
            try:
                tla_path.unlink()
            except OSError:
                pass

    except Exception as exc:
        logger.error("spec=%d model=%s condition=%s: %s", spec_id, model_id, condition, exc, exc_info=True)
        return _base_record(str(exc))


def _log_to_wandb(model_cfg: dict, conditions: list[str], results: list[dict],
                  wandb_project: str, wandb_entity: str | None) -> None:
    import wandb

    model_id = model_cfg["id"]
    run = wandb.init(
        project=wandb_project, entity=wandb_entity,
        name=f"eval_{model_id}", group="baseline_eval", job_type="eval",
        config={
            "model_id": model_id, "model_name": model_cfg.get("model_name", model_id),
            "backend": model_cfg.get("backend"), "temperature": model_cfg.get("temperature", 0.0),
            "conditions": conditions, "num_specs": len(results),
        },
    )

    try:
        spec_table = wandb.Table(columns=[
            "spec_id", "condition", "model_id", "complexity_tier",
            "sany_pass", "tlc_pass", "pass_at_1", "error",
        ])
        condition_stats = {c: {"total": 0, "sany": 0, "tlc": 0, "pass1": 0} for c in conditions}
        tier_stats = {t: {"total": 0, "sany": 0, "tlc": 0, "pass1": 0} for t in KNOWN_TIERS}

        for r in results:
            s, t, p1 = int(bool(r.get("sany_pass"))), int(bool(r.get("tlc_pass"))), int(bool(r.get("pass_at_1")))
            cond, tier = r.get("condition", ""), r.get("complexity_tier", "unknown")
            spec_table.add_data(r.get("spec_id"), cond, model_id, tier, bool(s), bool(t), bool(p1), r.get("error") or "")
            if cond in condition_stats:
                cs = condition_stats[cond]
                cs["total"] += 1; cs["sany"] += s; cs["tlc"] += t; cs["pass1"] += p1
            if tier in tier_stats:
                ts = tier_stats[tier]
                ts["total"] += 1; ts["sany"] += s; ts["tlc"] += t; ts["pass1"] += p1

        total_all = sum(s["total"] for s in condition_stats.values())
        sany_all  = sum(s["sany"]  for s in condition_stats.values())
        tlc_all   = sum(s["tlc"]   for s in condition_stats.values())
        pass1_all = sum(s["pass1"] for s in condition_stats.values())

        metrics: dict[str, float] = {
            "eval/overall_sany_rate":  sany_all  / total_all if total_all else 0.0,
            "eval/overall_tlc_rate":   tlc_all   / total_all if total_all else 0.0,
            "eval/overall_pass1_rate": pass1_all / total_all if total_all else 0.0,
            "eval/total_specs": float(total_all),
        }
        for cond, stats in condition_stats.items():
            n = stats["total"]
            metrics[f"eval/{cond}/sany_rate"]  = stats["sany"]  / n if n else 0.0
            metrics[f"eval/{cond}/tlc_rate"]   = stats["tlc"]   / n if n else 0.0
            metrics[f"eval/{cond}/pass1_rate"] = stats["pass1"] / n if n else 0.0
        for tier, stats in tier_stats.items():
            n = stats["total"]
            if n == 0:
                continue
            metrics[f"eval/{tier}/sany_rate"]  = stats["sany"]  / n
            metrics[f"eval/{tier}/tlc_rate"]   = stats["tlc"]   / n
            metrics[f"eval/{tier}/pass1_rate"] = stats["pass1"] / n
            metrics[f"eval/{tier}/total"]      = float(n)

        wandb.log(metrics)
        wandb.log({"results/spec_table": spec_table})
        wandb.summary.update(metrics)
    finally:
        run.finish()


def run_all(
    model_cfg: dict[str, Any],
    test_ids: list[int],
    conditions: list[str],
    api_key: str = "",
    gpu_id: int = 0,
    wandb_project: str = "tla_bench",
    wandb_entity: str | None = None,
    use_wandb: bool = True,
    workers: int = 4,
    resume: bool = False,
) -> list[dict[str, Any]]:
    if api_key:
        os.environ.setdefault("OPENAI_API_KEY", api_key)
        os.environ.setdefault("ANTHROPIC_API_KEY", api_key)
        os.environ.setdefault("GEMINI_API_KEY", api_key)
    os.environ["CUDA_VISIBLE_DEVICES"] = str(gpu_id)

    templates = {
        cond: load_text(repo_root() / "configs/prompts" / fname)
        for cond, fname in _PROMPT_TEMPLATE_FOR.items()
    }

    model_id = model_cfg["id"]
    ckpt = CheckpointManager(model_id)
    if not resume:
        ckpt.clear()

    results: list[dict] = []
    pending: dict = {}
    t_start = time.time()

    with ThreadPoolExecutor(max_workers=workers) as pool:
        for spec_id in test_ids:
            spec_data = get_spec_by_id(spec_id)
            if spec_data is None:
                logger.warning("spec=%d: not found in dataset - skipping", spec_id)
                continue
            for condition in conditions:
                if ckpt.is_done(spec_id, condition):
                    results.append(ckpt.load_one(spec_id, condition))
                    continue
                fut = pool.submit(_process_spec, spec_id, condition, spec_data, model_cfg, templates)
                pending[fut] = (spec_id, condition)

        for fut in as_completed(pending):
            spec_id, condition = pending[fut]
            try:
                record = fut.result()
            except Exception as exc:
                logger.error("spec=%d condition=%s: worker error: %s", spec_id, condition, exc, exc_info=True)
                continue
            if record is not None:
                ckpt.save(record)
                results.append(record)
                logger.info("spec=%d condition=%s sany=%s tlc=%s", spec_id, condition,
                            record.get("sany_pass"), record.get("tlc_pass"))

    n = len(results)
    sany_rate = sum(1 for r in results if r.get("sany_pass")) / n if n else 0.0
    logger.info("model=%s done in %.1fs: %d results sany_rate=%.3f", model_id, time.time() - t_start, n, sany_rate)

    if use_wandb:
        try:
            _log_to_wandb(model_cfg, conditions, results, wandb_project, wandb_entity)
        except Exception as exc:
            logger.warning("W&B logging failed (results still saved): %s", exc)

    return results


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--model")
    parser.add_argument("--condition", choices=ALL_CONDITIONS + ["all"], default="all")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--no-wandb", action="store_true")
    parser.add_argument("--api-key", default="")
    parser.add_argument("--gpu-id", type=int, default=0)
    parser.add_argument("--wandb-project", default="tla_bench")
    parser.add_argument("--wandb-entity", default=None)
    args = parser.parse_args()

    models_cfg = load_json(repo_root() / "configs/models.json")
    split = load_json(data_dir() / "test_split.json")
    test_ids: list[int] = split["test_ids"]
    if args.limit:
        test_ids = test_ids[: args.limit]
    conditions = ALL_CONDITIONS if args.condition == "all" else [args.condition]

    for model_cfg in models_cfg:
        if args.model and model_cfg["id"] != args.model:
            continue
        results = run_all(
            model_cfg, test_ids, conditions,
            api_key=args.api_key, gpu_id=args.gpu_id,
            wandb_project=args.wandb_project, wandb_entity=args.wandb_entity,
            use_wandb=not args.no_wandb, workers=args.workers, resume=args.resume,
        )
        out = outputs_dir() / f"run_{model_cfg['id']}.json"
        save_json(results, out)
        logger.info("Saved %d results → %s", len(results), out)


if __name__ == "__main__":
    main()
