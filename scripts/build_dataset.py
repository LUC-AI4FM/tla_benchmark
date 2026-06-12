#!/usr/bin/env python3
from __future__ import annotations

import json
import random
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))

from utils import data_dir, get_logger, save_json

logger = get_logger("build_dataset")

PARSED_DIR  = data_dir() / "parsed"
TLA_DIR     = data_dir() / "tla_files"
INDEX_PATH  = data_dir() / "index.json"
DESC_DIR    = data_dir() / "descriptions"
SPLIT_PATH  = data_dir() / "test_split.json"

TEST_RATIO   = 0.20
RANDOM_SEED  = 42
MIN_SPEC_LEN = 200


def _tla_path(parsed_path: Path) -> Path:
    rel = parsed_path.relative_to(PARSED_DIR)
    tla_name = parsed_path.stem.replace("_v3", "") + ".tla"
    return TLA_DIR / rel.parent / tla_name


def build_index() -> list[dict]:
    parsed_files = sorted(PARSED_DIR.rglob("*_v3.json"))
    logger.info("found %d parsed files", len(parsed_files))

    records = []
    skipped = 0
    for spec_id, pf in enumerate(parsed_files):
        try:
            d = json.loads(pf.read_text(encoding="utf-8"))
        except Exception as exc:
            logger.warning("skip %s: %s", pf.name, exc)
            skipped += 1
            continue

        spec_text = (d.get("Specification") or "").strip()
        if len(spec_text) < MIN_SPEC_LEN:
            logger.warning("skip id=%d %s: spec too short (%d chars)", spec_id, pf.name, len(spec_text))
            skipped += 1
            continue

        tla = _tla_path(pf)
        if not tla.exists():
            logger.warning("skip id=%d %s: no tla file at %s", spec_id, pf.name, tla)
            skipped += 1
            continue

        records.append({
            "spec_id":        spec_id,
            "module_name":    d.get("ModuleName", pf.stem.replace("_v3", "")),
            "complexity_tier": d.get("ComplexityTier", "basic"),
            "specification":  spec_text,
            "parsed_path":    str(pf.relative_to(REPO_ROOT)),
            "tla_path":       str(tla.relative_to(REPO_ROOT)),
        })

    logger.info("indexed %d specs, skipped %d", len(records), skipped)
    return records


def write_descriptions(records: list[dict]) -> None:
    DESC_DIR.mkdir(parents=True, exist_ok=True)
    for r in records:
        txt_path = DESC_DIR / f"{r['spec_id']}.txt"
        txt_path.write_text(r["specification"], encoding="utf-8")
    logger.info("wrote %d description files to %s", len(records), DESC_DIR)


def build_split(records: list[dict]) -> dict:
    by_tier: dict[str, list[int]] = defaultdict(list)
    for r in records:
        by_tier[r["complexity_tier"]].append(r["spec_id"])

    rng = random.Random(RANDOM_SEED)
    test_ids: list[int] = []
    train_ids: list[int] = []

    for tier, ids in sorted(by_tier.items()):
        shuffled = ids[:]
        rng.shuffle(shuffled)
        n_test = max(1, round(len(shuffled) * TEST_RATIO))
        test_ids.extend(shuffled[:n_test])
        train_ids.extend(shuffled[n_test:])

    test_ids.sort()
    train_ids.sort()

    tier_counts = {t: len(ids) for t, ids in by_tier.items()}
    logger.info("split: %d train, %d test | tiers: %s", len(train_ids), len(test_ids), tier_counts)
    return {"train_ids": train_ids, "test_ids": test_ids}


def main() -> None:
    records = build_index()

    index = {str(r["spec_id"]): r for r in records}
    save_json(index, INDEX_PATH)
    logger.info("saved index: %s", INDEX_PATH)

    write_descriptions(records)

    split = build_split(records)
    save_json(split, SPLIT_PATH)
    logger.info("saved split: %s", SPLIT_PATH)

    tiers = defaultdict(int)
    for r in records:
        tiers[r["complexity_tier"]] += 1
    print(f"total specs: {len(records)}")
    print(f"train: {len(split['train_ids'])}  test: {len(split['test_ids'])}")
    for t, n in sorted(tiers.items()):
        print(f"  {t}: {n}")


if __name__ == "__main__":
    main()
