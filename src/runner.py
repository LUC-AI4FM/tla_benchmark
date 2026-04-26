from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import (
    data_dir, get_logger, load_json, load_text, outputs_dir, repo_root,
    retry_with_backoff, save_json, save_text,
)
from parser import extract_tla_from_response, merge_step_outputs
from validator import validate_spec

logger = get_logger("runner")


def _call_ollama(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import requests
    payload = {
        "model": model_name,
        "prompt": prompt,
        "stream": False,
        "options": {"temperature": temperature, "num_predict": max_tokens},
    }
    resp = requests.post("http://localhost:11434/api/generate", json=payload, timeout=300)
    resp.raise_for_status()
    data = resp.json()
    return {
        "text": data.get("response", ""),
        "tokens_in": data.get("prompt_eval_count", 0),
        "tokens_out": data.get("eval_count", 0),
    }


def _call_openai(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    client = openai.OpenAI()
    response = client.chat.completions.create(
        model=model_name,
        messages=[{"role": "user", "content": prompt}],
        temperature=temperature,
        max_tokens=max_tokens,
    )
    choice = response.choices[0]
    return {
        "text": choice.message.content or "",
        "tokens_in": response.usage.prompt_tokens if response.usage else 0,
        "tokens_out": response.usage.completion_tokens if response.usage else 0,
    }


def _call_model(cfg: dict[str, Any], prompt: str) -> dict[str, Any]:
    backend = cfg["backend"]
    model_name = cfg["model_name"]
    temperature = cfg.get("temperature", 0.0)
    max_tokens = cfg.get("max_tokens", 8192)

    if backend == "ollama":
        return _call_ollama(model_name, prompt, temperature, max_tokens)
    elif backend == "openai":
        return _call_openai(model_name, prompt, temperature, max_tokens)
    else:
        raise ValueError(f"Unknown backend: {backend}")


def run_single_spec(spec_id: str, spec_version: str, model_cfg: dict, prompt_name: str, condition: str, api_key: str, gpu_id: int):
    os.environ["OPENAI_API_KEY"] = api_key
    os.environ["CUDA_VISIBLE_DEVICES"] = str(gpu_id)
    
    logger.info(f"Running spec {spec_id} with model {model_cfg['model_name']} on GPU {gpu_id}")

    run = wandb.init(
        project="tla",
        name=f"{spec_id}_{model_cfg['id']}",
        config=model_cfg,
    )

    _call_model(model_cfg, prompt_name)

    run.finish()


def _build_progressive_messages(base_prompt: str, model_cfg: dict) -> tuple[list[dict[str, Any]], list[str]]:
    conversation = []
    step_outputs = []
    total_tokens_in = 0
    total_tokens_out = 0

    for i, step_instruction in enumerate(_STEP_PROMPTS):
        if i == 0:
            prompt = base_prompt + "\n\n" + step_instruction
        else:
            prior = "\n".join(step_outputs)
            prompt = f"Prior output so far:\n{prior}\n\n{step_instruction}"

        conversation.append({"role": "user", "content": prompt, "step": i + 1})

        def call(p=prompt):
            return _call_model(model_cfg, p)

        t0 = time.time()
        result = retry_with_backoff(call)
        elapsed = round(time.time() - t0, 2)

        total_tokens_in += result["tokens_in"]
        total_tokens_out += result["tokens_out"]
        step_outputs.append(result["text"])

        logger.info(
            "step=%d/%d model=%s tokens_in=%d tokens_out=%d latency=%.2fs",
            i + 1, len(_STEP_PROMPTS), model_cfg["id"],
            result["tokens_in"], result["tokens_out"], elapsed,
        )

        conversation.append({
            "role": "assistant",
            "content": result["text"],
            "step": i + 1,
            "tokens_in": result["tokens_in"],
            "tokens_out": result["tokens_out"],
            "latency_s": elapsed,
        })

    logger.info(
        "progressive_prompt done: model=%s total_tokens_in=%d total_tokens_out=%d steps=%d",
        model_cfg["id"], total_tokens_in, total_tokens_out, len(_STEP_PROMPTS),
    )
    return conversation, step_outputs


def _get_cfg_path(spec_id: int, module_name: str) -> str | None:
    direct = data_dir() / "cfg" / f"{spec_id}.cfg"
    if direct.exists():
        return str(direct)
    return None


def run_all(model_cfg: dict[str, Any], test_ids: list[int], conditions: list[str]) -> list[dict[str, Any]]:
    templates = {
        cond: load_text(repo_root() / "configs/prompts" / fname)
        for cond, fname in _PROMPT_TEMPLATE_FOR.items()
    }

    results = []
    for spec_id in test_ids:
        v2_path = data_dir() / "v2_json" / f"{spec_id}.json"
        if not v2_path.exists():
            logger.warning("spec=%s: no v2 JSON (needed for module name), skipping all conditions", spec_id)
            continue

        v2_data = load_json(v2_path)
        module_name = v2_data.get("ModuleName", str(spec_id))

        for condition in conditions:
            input_text = _resolve_input(spec_id, condition, v2_data)
            if input_text is None:
                continue

            try:
                summary = run_single_spec(spec_id, model_cfg, prompt_name, condition, api_key, gpu_id)
                results.append(summary)
            except Exception as exc:
                logger.error("spec=%s model=%s condition=%s: %s", spec_id, model_cfg["id"], condition, exc)
                results.append({
                    "spec_id": spec_id,
                    "model_id": model_cfg["id"],
                    "condition": condition,
                    "sany_pass": False,
                    "tlc_pass": False,
                    "error": str(exc),
                })

    return results


def main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--model", help="Model ID to run (default: all)")
    parser.add_argument(
        "--condition",
        choices=ALL_CONDITIONS + ["all"],
        default="all",
        help="Condition to run (default: all three)",
    )
    parser.add_argument("--limit", type=int, default=None, help="Limit number of test specs")
    args = parser.parse_args()

    models_cfg = load_json(repo_root() / "configs/models.json")
    split = load_json(data_dir() / "test_split.json")
    test_ids = split["test_ids"]
    if args.limit:
        test_ids = test_ids[:args.limit]

    conditions = ALL_CONDITIONS if args.condition == "all" else [args.condition]

    for model_cfg in models_cfg:
        if args.model and model_cfg["id"] != args.model:
            continue
        logger.info("Running model: %s", model_cfg["id"])
        results = run_all(model_cfg, test_ids, conditions)
        save_json(results, outputs_dir() / f"run_{model_cfg['id']}.json")
        logger.info("Completed model: %s, results: %d", model_cfg["id"], len(results))


if __name__ == "__main__":
    main()
