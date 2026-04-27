from __future__ import annotations

import argparse
import importlib
import json
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

sys.path.insert(0, str(Path(__file__).parent))

from parser import extract_tla_from_response
from utils import (
    data_dir, get_logger, load_json, load_text, outputs_dir,
    repo_root, retry_with_backoff, save_json, save_text,
)
from validator import validate_spec

logger = get_logger("runner")

CONDITION_TEMPLATES: dict[str, str] = {
    "nlp_to_tla": "nlp_to_tla.txt",
    "v2_to_tla": "json_to_tla.txt",
    "v3_to_tla": "v3_to_tla.txt",
    "ast_to_tla": "ast_to_tla.txt",
}

ALL_CONDITIONS: list[str] = list(CONDITION_TEMPLATES.keys())


def _call_ollama(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import requests

    ollama_url = os.getenv("OLLAMA_URL", "http://localhost:11434")
    payload = {
        "model": model_name,
        "prompt": prompt,
        "stream": False,
        "options": {"temperature": temperature, "num_predict": max_tokens},
    }
    resp = requests.post(f"{ollama_url}/api/generate", json=payload, timeout=600)
    resp.raise_for_status()
    body = resp.json()
    return {
        "text": body.get("response", ""),
        "tokens_in": body.get("prompt_eval_count", 0),
        "tokens_out": body.get("eval_count", 0),
    }


def _call_openai(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import openai

    client = openai.OpenAI()
    response = client.chat.completions.create(
        model=model_name,
        messages=[{"role": "user", "content": prompt}],
        temperature=temperature,
        max_tokens=max_tokens,
    )
    choice = response.choices[0]
    usage = response.usage
    return {
        "text": choice.message.content or "",
        "tokens_in": usage.prompt_tokens if usage else 0,
        "tokens_out": usage.completion_tokens if usage else 0,
    }


_BACKEND_DISPATCH: dict[str, Any] = {
    "ollama": _call_ollama,
    "openai": _call_openai,
}


def _call_model(cfg: dict[str, Any], prompt: str, temperature: float | None = None) -> dict[str, Any]:
    backend = cfg["backend"]
    if backend not in _BACKEND_DISPATCH:
        raise ValueError(f"Unknown backend '{backend}'. Supported: {list(_BACKEND_DISPATCH.keys())}")
    return _BACKEND_DISPATCH[backend](
        model_name=cfg["model_name"],
        prompt=prompt,
        temperature=temperature if temperature is not None else cfg.get("temperature", 0.0),
        max_tokens=cfg.get("max_tokens", 8192),
    )


def _resolve_input(spec_id: int, condition: str) -> Optional[str]:
    if condition == "nlp_to_tla":
        desc_path = data_dir() / "descriptions" / f"{spec_id}.json"
        if not desc_path.exists():
            return None
        return json.dumps(load_json(desc_path), indent=2)
    elif condition == "v2_to_tla":
        json_path = data_dir() / "v2_json" / f"{spec_id}.json"
        if not json_path.exists():
            return None
        return json.dumps(load_json(json_path), indent=2)
    elif condition == "v3_to_tla":
        json_path = data_dir() / "v3_json" / f"{spec_id}.json"
        if not json_path.exists():
            return None
        return json.dumps(load_json(json_path), indent=2)
    elif condition == "ast_to_tla":
        json_path = data_dir() / "ast_json" / f"{spec_id}.json"
        if not json_path.exists():
            return None
        return json.dumps(load_json(json_path), indent=2)
    else:
        logger.error("Unknown condition: %s", condition)
        return None


def _build_prompt(condition: str, input_text: str) -> str:
    template_file = CONDITION_TEMPLATES[condition]
    template = load_text(repo_root() / "configs" / "prompts" / template_file)

    if "{description}" in template:
        return template.replace("{description}", input_text)
    elif "{json_content}" in template:
        return template.replace("{json_content}", input_text)
    else:
        return template + "\n" + input_text


def _get_cfg_path(spec_id: int) -> Optional[str]:
    cfg_file = data_dir() / "cfg" / f"{spec_id}.cfg"
    if cfg_file.exists():
        return str(cfg_file)
    return None


def run_single_sample(
    spec_id: int,
    condition: str,
    model_cfg: dict[str, Any],
    sample_index: int,
    prompt: str,
    temperature: float,
) -> dict[str, Any]:
    model_id = model_cfg["id"]
    base = outputs_dir()

    raw_dir = base / "raw" / model_id / condition / str(spec_id)
    raw_dir.mkdir(parents=True, exist_ok=True)

    extracted_dir = base / "extracted" / model_id / condition / str(spec_id)
    extracted_dir.mkdir(parents=True, exist_ok=True)

    validation_dir = base / "validation" / model_id / condition / str(spec_id)
    validation_dir.mkdir(parents=True, exist_ok=True)

    t0 = time.time()

    def _generate():
        return _call_model(model_cfg, prompt, temperature=temperature)

    result = retry_with_backoff(_generate, max_attempts=3, base_delay=2.0)
    latency = round(time.time() - t0, 2)
    timestamp = datetime.now(timezone.utc).isoformat()

    raw_record = {
        "spec_id": spec_id, "model_id": model_id, "condition": condition,
        "sample_index": sample_index, "response_text": result["text"],
        "tokens_in": result["tokens_in"], "tokens_out": result["tokens_out"],
        "latency_s": latency, "temperature": temperature, "timestamp": timestamp,
    }
    save_json(raw_record, raw_dir / f"sample_{sample_index}.json")

    logger.info(
        "generated  spec=%d model=%s cond=%s sample=%d tokens_out=%d latency=%.1fs",
        spec_id, model_id, condition, sample_index, result["tokens_out"], latency,
    )

    extracted_tla = extract_tla_from_response(result["text"])
    has_tla = extracted_tla is not None

    if has_tla:
        tla_path = extracted_dir / f"sample_{sample_index}.tla"
        save_text(extracted_tla, tla_path)
    else:
        tla_path = None

    sany_pass = False
    tlc_pass = False

    if tla_path is not None:
        cfg_path = _get_cfg_path(spec_id)
        val_result = validate_spec(
            tla_path=str(tla_path), cfg_path=cfg_path,
            validation_out_dir=str(validation_dir),
            spec_id=f"{spec_id}_sample_{sample_index}",
            model_id=model_id, condition=condition,
        )
        sany_pass = val_result.get("sany_pass", False)
        tlc_pass = val_result.get("tlc_pass", False)

    summary = {
        "spec_id": spec_id, "model_id": model_id, "condition": condition,
        "sample_index": sample_index, "has_tla": has_tla,
        "sany_pass": sany_pass, "tlc_pass": tlc_pass,
        "tokens_in": result["tokens_in"], "tokens_out": result["tokens_out"],
        "latency_s": latency, "temperature": temperature, "timestamp": timestamp,
    }
    save_json(summary, validation_dir / f"sample_{sample_index}_summary.json")
    return summary


def run_batch(
    model_cfg: dict[str, Any],
    test_ids: list[int],
    conditions: list[str],
    num_samples: int = 10,
    temperature: float = 0.8,
) -> list[dict[str, Any]]:
    model_id = model_cfg["id"]
    all_summaries: list[dict[str, Any]] = []
    total_tasks = len(test_ids) * len(conditions) * num_samples
    completed = 0

    for spec_id in test_ids:
        for condition in conditions:
            input_text = _resolve_input(spec_id, condition)
            if input_text is None:
                completed += num_samples
                continue

            prompt = _build_prompt(condition, input_text)

            for sample_i in range(num_samples):
                try:
                    summary = run_single_sample(
                        spec_id=spec_id, condition=condition, model_cfg=model_cfg,
                        sample_index=sample_i, prompt=prompt, temperature=temperature,
                    )
                    all_summaries.append(summary)
                except Exception as exc:
                    logger.error(
                        "failed  spec=%d model=%s cond=%s sample=%d: %s",
                        spec_id, model_id, condition, sample_i, exc,
                    )
                    all_summaries.append({
                        "spec_id": spec_id, "model_id": model_id,
                        "condition": condition, "sample_index": sample_i,
                        "has_tla": False, "sany_pass": False, "tlc_pass": False,
                        "error": str(exc),
                        "timestamp": datetime.now(timezone.utc).isoformat(),
                    })

                completed += 1
                if completed % 10 == 0 or completed == total_tasks:
                    logger.info(
                        "progress  model=%s  %d/%d (%.0f%%)",
                        model_id, completed, total_tasks, 100 * completed / total_tasks,
                    )

    return all_summaries


def main() -> None:
    parser = argparse.ArgumentParser(description="TLA+Bench multi-sample evaluation runner.")
    parser.add_argument("--model", default=None)
    parser.add_argument("--condition", choices=ALL_CONDITIONS + ["all"], default="all")
    parser.add_argument("--num_samples", type=int, default=10)
    parser.add_argument("--temperature", type=float, default=0.8)
    parser.add_argument("--limit", type=int, default=None)
    args = parser.parse_args()

    models_cfg = load_json(repo_root() / "configs" / "models.json")
    split = load_json(data_dir() / "test_split.json")
    test_ids: list[int] = split["test_ids"]

    if args.limit:
        test_ids = test_ids[: args.limit]

    conditions = ALL_CONDITIONS if args.condition == "all" else [args.condition]

    logger.info(
        "start  models=%d specs=%d conditions=%d samples=%d temp=%.2f",
        len(models_cfg) if not args.model else 1,
        len(test_ids), len(conditions), args.num_samples, args.temperature,
    )

    for model_cfg in models_cfg:
        if args.model and model_cfg["id"] != args.model:
            continue

        logger.info("=== model: %s ===", model_cfg["id"])

        summaries = run_batch(
            model_cfg=model_cfg, test_ids=test_ids, conditions=conditions,
            num_samples=args.num_samples, temperature=args.temperature,
        )

        batch_path = outputs_dir() / f"batch_{model_cfg['id']}.json"
        save_json(summaries, batch_path)

        passed = sum(1 for s in summaries if s.get("sany_pass"))
        tlc_ok = sum(1 for s in summaries if s.get("tlc_pass"))

        logger.info(
            "=== done: %s  total=%d sany=%d tlc=%d ===",
            model_cfg["id"], len(summaries), passed, tlc_ok,
        )

    logger.info("pipeline complete")


if __name__ == "__main__":
    main()
