from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import (
    data_dir, get_logger, get_spec_by_id, get_tla_path,
    load_text, outputs_dir, repo_root,
)
from validator import validate_spec
from parser import extract_tla_from_response
from runner import _call_model, _resolve_input

logger = get_logger("preference_generator")


def _get_ground_truth_tla(spec_id: int) -> str | None:
    tla_path = get_tla_path(spec_id)
    if tla_path is None:
        return None
    return tla_path.read_text(encoding="utf-8")


def _build_prompt(spec_id: int, spec_data: dict) -> str | None:
    prompt_file = repo_root() / "configs" / "prompts" / "nlp_to_tla.txt"
    if not prompt_file.exists():
        logger.warning("missing prompt file: %s", prompt_file)
        return None
    description = _resolve_input(spec_id, "nlp_to_tla", spec_data)
    if not description:
        logger.warning("spec=%d: no description available, skipping", spec_id)
        return None
    template = load_text(prompt_file)
    return template.replace("{description}", description)


def _validate_tla(tla_source: str, spec_id: int, label: str) -> tuple[bool, bool]:
    tmp_dir = Path(tempfile.mkdtemp(prefix="pref_val_"))
    tmp_tla = tmp_dir / f"{label}.tla"
    tmp_tla.write_text(tla_source)
    try:
        cfg_path = data_dir() / "cfg" / f"{spec_id}.cfg"
        summary = validate_spec(
            str(tmp_tla),
            str(cfg_path) if cfg_path.exists() else None,
            str(tmp_dir),
            spec_id,
            label,
            "nlp_to_tla",
        )
        return summary.get("sany_pass", False), summary.get("tlc_pass", False)
    except Exception as exc:
        logger.error("spec=%d validation error (%s): %s", spec_id, label, exc)
        return False, False
    finally:
        import shutil
        shutil.rmtree(tmp_dir, ignore_errors=True)


def _get_ground_truth_search_paths(spec_id: int) -> list[str]:
    from utils import get_tla_path
    tla_path = get_tla_path(spec_id)
    if tla_path is None:
        return []
    tla_files_root = data_dir() / "tla_files"
    paths: list[str] = []
    current = tla_path.parent
    while True:
        paths.append(str(current))
        if current == tla_files_root or current == current.parent:
            break
        current = current.parent
    return paths


def generate_preference_dataset(
    spec_ids: list[int],
    model_config: dict[str, Any],
    num_candidates: int = 5,
    output_path: Path | None = None,
) -> list[dict[str, Any]]:
    if output_path is None:
        output_path = outputs_dir() / "preference_dataset.jsonl"

    all_pairs = []

    for spec_id in spec_ids:
        spec_data = get_spec_by_id(spec_id)
        if spec_data is None:
            logger.warning("spec=%d: not found in dataset, skipping", spec_id)
            continue

        chosen = _get_ground_truth_tla(spec_id)
        if not chosen:
            logger.warning("spec=%d: no ground-truth TLA+ file, skipping", spec_id)
            continue
        # ground truth is real production TLA+ — trust it without re-validating
        # in isolation (EXTENDS project-local modules would fail SANY without
        # the full repo module search path)
        chosen_passes_tlc = False

        prompt = _build_prompt(spec_id, spec_data)
        if not prompt:
            continue

        # preference priority:
        #   tier 1 (strongest): sany-pass + tlc-fail  (semantically wrong, syntax ok)
        #   tier 2 (fallback):  sany-fail              (syntactically wrong)
        rejected_tier1 = None
        rejected_tier2 = None

        for attempt in range(num_candidates):
            try:
                result = _call_model(model_config, prompt)
                extracted = extract_tla_from_response(result["text"])
                if not extracted:
                    continue
                sany_ok, tlc_ok = _validate_tla(extracted, spec_id, f"{model_config['id']}_attempt{attempt}")
                if sany_ok and not tlc_ok and rejected_tier1 is None:
                    rejected_tier1 = extracted
                elif not sany_ok and rejected_tier2 is None:
                    rejected_tier2 = extracted
                if rejected_tier1 is not None:
                    break
            except Exception as exc:
                logger.error("spec=%d attempt=%d: %s", spec_id, attempt, exc)

        rejected = rejected_tier1 or rejected_tier2
        rejection_type = "tlc_fail" if rejected_tier1 else "sany_fail" if rejected_tier2 else None

        if rejected is None:
            logger.warning("spec=%d: no rejected candidate found in %d attempts", spec_id, num_candidates)
            continue

        all_pairs.append({
            "spec_id":          spec_id,
            "condition":        "nlp_to_tla",
            "prompt":           prompt,
            "chosen":           chosen,
            "chosen_tlc_pass":  chosen_passes_tlc,
            "rejected":         rejected,
            "rejection_type":   rejection_type,
        })
        logger.info("spec=%d: pair added type=%s (total: %d)", spec_id, rejection_type, len(all_pairs))

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        for pair in all_pairs:
            f.write(json.dumps(pair) + "\n")

    tier1 = sum(1 for p in all_pairs if p["rejection_type"] == "tlc_fail")
    tier2 = sum(1 for p in all_pairs if p["rejection_type"] == "sany_fail")
    logger.info("saved: %s (%d pairs: %d tlc_fail + %d sany_fail)", output_path, len(all_pairs), tier1, tier2)
    return all_pairs


def main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--limit",      type=int,  default=None)
    parser.add_argument("--candidates", type=int,  default=5)
    parser.add_argument("--model",      type=str,  default="qwen2.5-coder:32b")
    parser.add_argument("--output",     type=Path, default=None)
    args = parser.parse_args()

    split    = load_json(data_dir() / "test_split.json")
    spec_ids = split["train_ids"]
    if args.limit:
        spec_ids = spec_ids[:args.limit]

    model_cfg = {
        "id":          args.model,
        "backend":     "ollama",
        "model_name":  args.model,
        "temperature": 0.7,
        "max_tokens":  4096,
    }

    logger.info("generating preference dataset: %d train specs model=%s candidates=%d",
                len(spec_ids), args.model, args.candidates)

    generate_preference_dataset(
        spec_ids=spec_ids,
        model_config=model_cfg,
        num_candidates=args.candidates,
        output_path=args.output,
    )


if __name__ == "__main__":
    main()
