from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import (
    data_dir, get_logger, get_spec_by_id, load_json, load_text, outputs_dir, repo_root,
    retry_with_backoff, save_json, save_text,
)
from parser import extract_tla_from_response, merge_step_outputs
from validator import validate_spec

logger = get_logger("runner")

_PROMPT_TEMPLATE_FOR = {
    "nlp_to_tla": "nlp_to_tla.txt",
    "v2_to_tla": "json_to_tla.txt",
    "v3_to_tla": "json_to_tla.txt",
}

ALL_CONDITIONS = list(_PROMPT_TEMPLATE_FOR.keys())

_STEP_PROMPTS = [
    "Step 1: Identify all constants and variables from the specification.",
    "Step 2: Define the initial state (Init predicate).",
    "Step 3: Define the next-state action (Next predicate).",
    "Step 4: Specify the temporal properties and invariants.",
    "Step 5: Combine all parts into a complete TLA+ module.",
]


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
    import openai
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


def _call_anthropic(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import requests
    import os
    
    api_key = os.environ.get("ANTHROPIC_API_KEY", os.environ.get("OPENAI_API_KEY", ""))
    if not api_key:
        raise ValueError("ANTHROPIC_API_KEY is not set.")
        
    payload = {
        "model": model_name,
        "max_tokens": max_tokens,
        "temperature": temperature,
        "messages": [{"role": "user", "content": prompt}],
    }
    
    headers = {
        "x-api-key": api_key,
        "anthropic-version": "2023-06-01",
        "content-type": "application/json",
    }
    
    resp = requests.post("https://api.anthropic.com/v1/messages", headers=headers, json=payload, timeout=300)
    resp.raise_for_status()
    data = resp.json()
    
    usage = data.get("usage", {})
    text = ""
    for c in data.get("content", []):
        text += c.get("text", "")
        
    return {
        "text": text,
        "tokens_in": usage.get("input_tokens", 0),
        "tokens_out": usage.get("output_tokens", 0),
    }


def _call_google(model_name: str, prompt: str, temperature: float, max_tokens: int) -> dict[str, Any]:
    import requests
    import os
    
    api_key = os.environ.get("GEMINI_API_KEY", os.environ.get("OPENAI_API_KEY", ""))
    if not api_key:
        raise ValueError("GEMINI_API_KEY is not set.")
        
    payload = {
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {
            "temperature": temperature,
            "maxOutputTokens": max_tokens
        }
    }
    
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent?key={api_key}"
    resp = requests.post(url, headers={"Content-Type": "application/json"}, json=payload, timeout=300)
    resp.raise_for_status()
    data = resp.json()
    
    try:
        text = data["candidates"][0]["content"]["parts"][0]["text"]
    except (KeyError, IndexError):
        text = ""
        
    usage = data.get("usageMetadata", {})
    return {
        "text": text,
        "tokens_in": usage.get("promptTokenCount", 0),
        "tokens_out": usage.get("candidatesTokenCount", 0),
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
    elif backend == "anthropic":
        return _call_anthropic(model_name, prompt, temperature, max_tokens)
    elif backend == "google":
        return _call_google(model_name, prompt, temperature, max_tokens)
    else:
        raise ValueError(f"Unknown backend: {backend}")


def run_single_spec(
    spec_id: str,
    spec_version: str,
    model_cfg: dict,
    prompt_name: str,
    condition: str,
    api_key: str,
    gpu_id: int,
    wandb_project: str = "tla_bench",
    wandb_entity: str = "",
    wandb_api_key: str = "",
):
    import wandb
    os.environ["OPENAI_API_KEY"] = api_key
    os.environ["CUDA_VISIBLE_DEVICES"] = str(gpu_id)
    if wandb_api_key:
        os.environ["WANDB_API_KEY"] = wandb_api_key

    logger.info("Running spec %s with model %s on GPU %d", spec_id, model_cfg["model_name"], gpu_id)

    run = wandb.init(
        project=wandb_project or "tla_bench",
        entity=wandb_entity or None,
        name=f"{spec_id}_{model_cfg['id']}",
        config={**model_cfg, "spec_id": spec_id, "spec_version": spec_version, "condition": condition},
    )

    result = _call_model(model_cfg, prompt_name)
    wandb.log({
        "tokens_in": result.get("tokens_in", 0),
        "tokens_out": result.get("tokens_out", 0),
        "response_len": len(result.get("text", "")),
    })

    run.finish()
    return result


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


def _resolve_input(spec_id: int, condition: str, v2_data: dict) -> str | None:
    if condition == "nlp_to_tla":
        desc_path_txt = data_dir() / "descriptions" / f"{spec_id}.txt"
        desc_path_json = data_dir() / "descriptions" / f"{spec_id}.json"
        
        if desc_path_txt.exists():
            return load_text(desc_path_txt)
        elif desc_path_json.exists():
            import json
            j_data = load_json(desc_path_json)
            out_lines = []
            for k, v in j_data.items():
                if k == "expected_output_files": continue
                if isinstance(v, list):
                    v = ", ".join(v)
                out_lines.append(f"{k.replace('_', ' ').title()}:\n{v}\n")
            return "\n".join(out_lines)
    elif condition in ["v2_to_tla", "v3_to_tla"]:
        return json.dumps(v2_data)
    
    return None


def run_all(
    model_cfg: dict[str, Any],
    test_ids: list[int],
    conditions: list[str],
    api_key: str = "",
    gpu_id: int = 0,
    wandb_project: str = "tla_bench",
    wandb_entity: str | None = None,
) -> list[dict[str, Any]]:
    import wandb
    import os

    if api_key:
        os.environ["OPENAI_API_KEY"] = api_key
        os.environ["ANTHROPIC_API_KEY"] = api_key
        os.environ["GEMINI_API_KEY"] = api_key

    templates = {
        cond: load_text(repo_root() / "configs/prompts" / fname)
        for cond, fname in _PROMPT_TEMPLATE_FOR.items()
    }

    model_id = model_cfg["id"]

    run = wandb.init(
        project=wandb_project,
        entity=wandb_entity,
        name=f"eval_{model_id}",
        group="baseline_eval",
        job_type="eval",
        config={
            "model_id": model_id,
            "model_name": model_cfg.get("model_name", model_id),
            "backend": model_cfg.get("backend"),
            "temperature": model_cfg.get("temperature", 0.0),
            "conditions": conditions,
            "num_specs": len(test_ids),
        },
    )

    results = []
    spec_table = wandb.Table(columns=[
        "spec_id", "condition", "model_id",
        "sany_pass", "tlc_pass", "error",
    ])

    # Per-condition accumulators for summary metrics
    condition_stats: dict[str, dict] = {
        c: {"total": 0, "sany": 0, "tlc": 0} for c in conditions
    }
    error_accum: dict[str, list] = {}
    global_step = 0

    try:
        for spec_id in test_ids:
            spec_data = get_spec_by_id(spec_id)
            if spec_data is None:
                logger.warning("spec=%s: not found in consolidated data, skipping all conditions", spec_id)
                continue

            module_name = spec_data.get("ModuleName", str(spec_id))

            for condition in conditions:
                input_text = _resolve_input(spec_id, condition, spec_data)
                if input_text is None:
                    continue

                template = templates[condition]
                if "{description}" in template:
                    prompt_text = template.replace("{description}", input_text)
                elif "{json_content}" in template:
                    prompt_text = template.replace("{json_content}", input_text)
                else:
                    prompt_text = template

                sany_pass = False
                tlc_pass = False
                error_str = None

                try:
                    result = _call_model(model_cfg, prompt_text)
                    extracted = extract_tla_from_response(result["text"])

                    if not extracted:
                        logger.error("spec=%d model=%s condition=%s: extraction failed", spec_id, model_id, condition)
                        error_str = "extraction_failed"
                        results.append({
                            "spec_id": spec_id, "model_id": model_id,
                            "condition": condition, "sany_pass": False,
                            "tlc_pass": False, "error": error_str,
                        })
                    else:
                        val_dir = outputs_dir() / "validation" / model_id / condition
                        spec_val_dir = val_dir / str(spec_id)
                        spec_val_dir.mkdir(parents=True, exist_ok=True)
                        temp_path = str(spec_val_dir / f"{module_name}.tla")

                        with open(temp_path, "w") as f:
                            f.write(extracted)

                        try:
                            cfg_path = _get_cfg_path(spec_id, module_name)
                            summary = validate_spec(temp_path, cfg_path, str(val_dir), spec_id, model_id, condition)
                            results.append(summary)
                            sany_pass = summary.get("sany_pass", False)
                            tlc_pass = summary.get("tlc_pass", False)

                            # Accumulate error classifications from validator output
                            err_file = val_dir / f"{spec_id}_errors.json"
                            if err_file.exists():
                                err_cats = load_json(err_file)
                                for k, v in err_cats.items():
                                    error_accum.setdefault(k, []).append(int(v))
                        finally:
                            try:
                                os.unlink(temp_path)
                            except Exception:
                                pass

                except Exception as exc:
                    logger.error("spec=%s model=%s condition=%s: %s", spec_id, model_id, condition, exc)
                    error_str = str(exc)
                    results.append({
                        "spec_id": spec_id, "model_id": model_id,
                        "condition": condition, "sany_pass": False,
                        "tlc_pass": False, "error": error_str,
                    })

                # Per-step W&B log (one row per spec × condition)
                global_step += 1
                wandb.log({
                    f"spec/{condition}/sany_pass": int(sany_pass),
                    f"spec/{condition}/tlc_pass": int(tlc_pass),
                }, step=global_step)

                spec_table.add_data(spec_id, condition, model_id, sany_pass, tlc_pass, error_str or "")

                # Update running condition stats
                condition_stats[condition]["total"] += 1
                condition_stats[condition]["sany"] += int(sany_pass)
                condition_stats[condition]["tlc"] += int(tlc_pass)

        # --- Summary metrics logged once at the end ---
        summary_metrics: dict[str, float] = {}
        total_all = sum(s["total"] for s in condition_stats.values())
        sany_all = sum(s["sany"] for s in condition_stats.values())
        tlc_all = sum(s["tlc"] for s in condition_stats.values())

        summary_metrics["eval/overall_sany_rate"] = sany_all / total_all if total_all else 0.0
        summary_metrics["eval/overall_tlc_rate"] = tlc_all / total_all if total_all else 0.0
        summary_metrics["eval/total_specs"] = total_all

        for cond, stats in condition_stats.items():
            n = stats["total"]
            summary_metrics[f"eval/{cond}/sany_rate"] = stats["sany"] / n if n else 0.0
            summary_metrics[f"eval/{cond}/tlc_rate"] = stats["tlc"] / n if n else 0.0

        # Error classification rates across all failed specs
        for err_type, flags in error_accum.items():
            summary_metrics[f"errors/{err_type}"] = sum(flags) / len(flags) if flags else 0.0

        wandb.log(summary_metrics, step=global_step)
        wandb.log({"results/spec_table": spec_table}, step=global_step)
        wandb.summary.update(summary_metrics)

        logger.info(
            "model=%s overall sany_rate=%.3f tlc_rate=%.3f (%d specs)",
            model_id,
            summary_metrics.get("eval/overall_sany_rate", 0),
            summary_metrics.get("eval/overall_tlc_rate", 0),
            total_all,
        )

    finally:
        run.finish()

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
    parser.add_argument("--api-key", default="", help="OpenAI API key")
    parser.add_argument("--gpu-id", type=int, default=0, help="GPU ID to use")
    parser.add_argument("--wandb-project", default="tla_bench", help="W&B project name")
    parser.add_argument("--wandb-entity", default=None, help="W&B entity (team/user)")
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
        results = run_all(
            model_cfg, test_ids, conditions,
            api_key=args.api_key, gpu_id=args.gpu_id,
            wandb_project=args.wandb_project, wandb_entity=args.wandb_entity,
        )
        save_json(results, outputs_dir() / f"run_{model_cfg['id']}.json")
        logger.info("Completed model: %s, results: %d", model_cfg["id"], len(results))


if __name__ == "__main__":
    main()
