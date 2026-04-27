from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Optional

sys.path.insert(0, str(Path(__file__).parent))

from utils import (
    data_dir, get_logger, load_json, load_text, outputs_dir,
    repo_root, results_dir, save_json,
)

logger = get_logger("pvp_generator")


def _load_prompt(spec_id: int, condition: str) -> Optional[str]:
    template_map = {
        "nlp_to_tla": "nlp_to_tla.txt",
        "v2_to_tla": "json_to_tla.txt",
        "v3_to_tla": "v3_to_tla.txt",
        "ast_to_tla": "ast_to_tla.txt",
    }
    template_file = template_map.get(condition)
    if template_file is None:
        return None

    template_path = repo_root() / "configs" / "prompts" / template_file
    if not template_path.exists():
        return None

    template = load_text(template_path)

    if condition == "nlp_to_tla":
        input_path = data_dir() / "descriptions" / f"{spec_id}.json"
    elif condition == "v2_to_tla":
        input_path = data_dir() / "v2_json" / f"{spec_id}.json"
    elif condition == "v3_to_tla":
        input_path = data_dir() / "v3_json" / f"{spec_id}.json"
    elif condition == "ast_to_tla":
        input_path = data_dir() / "ast_json" / f"{spec_id}.json"
    else:
        return None

    if not input_path.exists():
        return None

    input_text = json.dumps(load_json(input_path), indent=2)

    if "{description}" in template:
        return template.replace("{description}", input_text)
    elif "{json_content}" in template:
        return template.replace("{json_content}", input_text)
    else:
        return template + "\n" + input_text


def _triplet_hash(prompt: str, chosen: str, rejected: str) -> str:
    content = f"{prompt}|||{chosen}|||{rejected}"
    return hashlib.sha256(content.encode()).hexdigest()[:16]


def generate_triplets(
    conditions: list[str] | None = None,
    max_rejected_per_chosen: int = 5,
) -> list[dict[str, str]]:
    if conditions is None:
        conditions = ["nlp_to_tla", "v2_to_tla", "v3_to_tla", "ast_to_tla"]

    validation_base = outputs_dir() / "validation"
    extracted_base = outputs_dir() / "extracted"

    if not validation_base.exists():
        logger.error("No validation outputs found.")
        return []

    SampleGroup = dict[str, list[dict[str, Any]]]
    groups: dict[tuple[str, str], SampleGroup] = defaultdict(
        lambda: {"chosen": [], "rejected": []}
    )

    for model_dir in sorted(validation_base.iterdir()):
        if not model_dir.is_dir():
            continue
        model_id = model_dir.name

        for cond_dir in sorted(model_dir.iterdir()):
            if not cond_dir.is_dir():
                continue
            condition = cond_dir.name
            if condition not in conditions:
                continue

            for spec_dir in sorted(cond_dir.iterdir()):
                if not spec_dir.is_dir():
                    continue
                spec_id = spec_dir.name

                for summary_file in sorted(spec_dir.glob("*_summary.json")):
                    summary = load_json(summary_file)
                    sample_name = summary_file.stem.replace("_summary", "")

                    tla_file = extracted_base / model_id / condition / spec_id / f"{sample_name}.tla"
                    if not tla_file.exists():
                        continue

                    tla_text = load_text(tla_file)
                    if not tla_text.strip():
                        continue

                    record = {
                        "model_id": model_id, "sample": sample_name,
                        "tla_text": tla_text,
                        "sany_pass": summary.get("sany_pass", False),
                        "tlc_pass": summary.get("tlc_pass", False),
                    }

                    key = (spec_id, condition)
                    if record["sany_pass"] and record["tlc_pass"]:
                        groups[key]["chosen"].append(record)
                    else:
                        groups[key]["rejected"].append(record)

    logger.info(
        "collected %d groups (%d with chosen)",
        len(groups),
        sum(1 for g in groups.values() if g["chosen"]),
    )

    triplets: list[dict[str, str]] = []
    seen_hashes: set[str] = set()

    for (spec_id, condition), group in sorted(groups.items()):
        chosen_list = group["chosen"]
        rejected_list = group["rejected"]

        if not chosen_list or not rejected_list:
            continue

        prompt = _load_prompt(int(spec_id), condition)
        if prompt is None:
            continue

        for chosen_rec in chosen_list:
            selected_rejected = rejected_list[:max_rejected_per_chosen]

            for rejected_rec in selected_rejected:
                h = _triplet_hash(prompt, chosen_rec["tla_text"], rejected_rec["tla_text"])
                if h in seen_hashes:
                    continue
                seen_hashes.add(h)

                triplets.append({
                    "prompt": prompt,
                    "chosen": chosen_rec["tla_text"],
                    "rejected": rejected_rec["tla_text"],
                })

    logger.info("generated %d unique triplets", len(triplets))
    return triplets


def export_triplets(
    triplets: list[dict[str, str]],
    val_fraction: float = 0.10,
    seed: int = 42,
) -> dict[str, Any]:
    output_dir = results_dir() / "pvp"
    output_dir.mkdir(parents=True, exist_ok=True)

    random.seed(seed)
    shuffled = triplets.copy()
    random.shuffle(shuffled)

    val_size = max(1, int(len(shuffled) * val_fraction))
    val_set = shuffled[:val_size]
    train_set = shuffled[val_size:]

    train_path = output_dir / "train.jsonl"
    val_path = output_dir / "val.jsonl"

    for dataset, path in [(train_set, train_path), (val_set, val_path)]:
        with open(path, "w", encoding="utf-8") as f:
            for item in dataset:
                f.write(json.dumps(item, ensure_ascii=False) + "\n")

    stats = {
        "total_triplets": len(triplets),
        "train_size": len(train_set), "val_size": len(val_set),
        "val_fraction": val_fraction, "seed": seed,
        "train_path": str(train_path), "val_path": str(val_path),
    }

    save_json(stats, output_dir / "stats.json")
    logger.info("exported  train=%d  val=%d", len(train_set), len(val_set))

    return stats


def main() -> None:
    parser = argparse.ArgumentParser(description="PVP triplet generator for DPO training.")
    parser.add_argument("--condition", default=None)
    parser.add_argument("--val_fraction", type=float, default=0.10)
    parser.add_argument("--max_rejected", type=int, default=5)
    parser.add_argument("--seed", type=int, default=42)
    args = parser.parse_args()

    conditions = [args.condition] if args.condition else None

    triplets = generate_triplets(conditions=conditions, max_rejected_per_chosen=args.max_rejected)

    if not triplets:
        logger.error("No triplets generated.")
        return

    stats = export_triplets(triplets, val_fraction=args.val_fraction, seed=args.seed)
    logger.info("done: %s", json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
