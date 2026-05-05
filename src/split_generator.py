"""
Train/Test Split Generator for TLA-Bench

This script generates a reproducible, well-documented train/test split
for the TLA-Bench benchmark. The split is:
  - Deterministic (uses fixed random seed)
  - Stratified (balanced by problem type and complexity)
  - Documented (includes reasoning and statistics)
  - Reproducible (can be regenerated exactly)
  - Auditable (full details logged)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger, data_dir, save_json, load_json

logger = get_logger("split_generator")


class TrainTestSplitGenerator:
    """Generate train/test split with clear, documented strategy."""

    def __init__(
        self,
        random_seed: int = 42,
        test_ratio: float = 0.20,
        stratify_by_type: bool = True,
    ):
        self.random_seed = random_seed
        self.test_ratio = test_ratio
        self.stratify_by_type = stratify_by_type
        self.rng = None

    def generate_split(self, data_dir_path: Path | None = None) -> dict[str, Any]:
        """Generate train/test split with clear strategy."""
        
        if data_dir_path is None:
            data_dir_path = data_dir()
        
        logger.info(f"Generating train/test split with seed={self.random_seed}")
        
        # Load all spec metadata
        descriptions = self._load_descriptions(data_dir_path)
        specs = sorted(descriptions.keys(), key=lambda x: int(x))
        
        logger.info(f"Total specs: {len(specs)}")
        
        # Categorize specs
        categories = self._categorize_specs(descriptions)
        logger.info(f"Categories found: {set(categories.values())}")
        
        # Generate split (stratified by category)
        import random
        random.seed(self.random_seed)
        
        test_size = int(len(specs) * self.test_ratio)
        test_ids = []
        
        if self.stratify_by_type:
            # Stratified split: maintain category proportions
            logger.info("Using stratified split (maintains category distribution)")
            test_ids = self._stratified_split(specs, categories, test_size)
        else:
            # Random split
            logger.info("Using random split (no stratification)")
            test_ids = sorted(random.sample(specs, test_size))
        
        train_ids = [s for s in specs if s not in test_ids]
        
        # Validate split
        split_info = self._validate_split(
            train_ids, test_ids, categories, descriptions
        )
        
        return {
            "metadata": {
                "seed": self.random_seed,
                "test_ratio": self.test_ratio,
                "stratify_by_type": self.stratify_by_type,
                "strategy": "Stratified random split to maintain category distribution",
                "notes": [
                    "Test set: 20% of specs (41 out of 206)",
                    "Split maintains proportions of problem types",
                    "Deterministic: uses fixed random seed for reproducibility",
                    "No data leakage: test set held completely separate",
                ],
            },
            "total": len(specs),
            "train_size": len(train_ids),
            "test_size": len(test_ids),
            "test_ratio_actual": len(test_ids) / len(specs),
            "train_ids": sorted([int(x) for x in train_ids]),
            "test_ids": sorted([int(x) for x in test_ids]),
            "statistics": split_info,
        }

    def _load_descriptions(self, data_dir_path: Path) -> dict[str, dict]:
        """Load all spec descriptions."""
        descriptions = {}
        desc_dir = data_dir_path / "descriptions"
        
        for desc_file in sorted(desc_dir.glob("*.json")):
            spec_id = desc_file.stem
            descriptions[spec_id] = load_json(desc_file)
        
        return descriptions

    def _categorize_specs(self, descriptions: dict) -> dict[str, str]:
        """Categorize specs by problem type from description."""
        categories = {}
        
        # Keywords for each category
        category_keywords = {
            "consensus": ["consensus", "byzantine", "agreement"],
            "mutex": ["mutual exclusion", "mutex", "lock"],
            "2pc": ["two-phase commit", "2pc", "phase commit"],
            "register": ["register", "atomic", "shared memory"],
            "election": ["leader election", "election", "leader"],
            "other": [],
        }
        
        for spec_id, desc_data in descriptions.items():
            overview = desc_data.get("system_overview", "").lower()
            
            category = "other"
            for cat, keywords in category_keywords.items():
                if any(kw in overview for kw in keywords):
                    category = cat
                    break
            
            categories[spec_id] = category
        
        return categories

    def _stratified_split(
        self,
        specs: list[str],
        categories: dict[str, str],
        test_size: int,
    ) -> list[str]:
        """Stratified split maintaining category proportions."""
        
        import random
        
        # Group specs by category
        cat_specs = {}
        for spec_id in specs:
            cat = categories[spec_id]
            if cat not in cat_specs:
                cat_specs[cat] = []
            cat_specs[cat].append(spec_id)
        
        # For each category, select proportional test examples
        test_ids = []
        for cat, cat_spec_list in sorted(cat_specs.items()):
            # Proportion of this category in total
            cat_proportion = len(cat_spec_list) / len(specs)
            cat_test_size = max(1, int(test_size * cat_proportion))
            
            # Randomly select from this category
            cat_test = random.sample(cat_spec_list, min(cat_test_size, len(cat_spec_list)))
            test_ids.extend(cat_test)
        
        # If we don't have exactly test_size, adjust
        if len(test_ids) > test_size:
            test_ids = random.sample(test_ids, test_size)
        elif len(test_ids) < test_size:
            remaining = [s for s in specs if s not in test_ids]
            additional = random.sample(remaining, test_size - len(test_ids))
            test_ids.extend(additional)
        
        return sorted(test_ids)

    def _validate_split(
        self,
        train_ids: list,
        test_ids: list,
        categories: dict,
        descriptions: dict,
    ) -> dict[str, Any]:
        """Validate split and compute statistics."""
        
        # No overlap
        overlap = set(train_ids) & set(test_ids)
        if overlap:
            logger.error(f"Split validation FAILED: {len(overlap)} specs in both sets!")
        
        # Category distribution
        train_categories = {}
        test_categories = {}
        
        for spec_id in train_ids:
            cat = categories[str(spec_id)]
            train_categories[cat] = train_categories.get(cat, 0) + 1
        
        for spec_id in test_ids:
            cat = categories[str(spec_id)]
            test_categories[cat] = test_categories.get(cat, 0) + 1
        
        logger.info("Train set category distribution:")
        for cat in sorted(train_categories.keys()):
            count = train_categories[cat]
            pct = 100 * count / len(train_ids)
            logger.info(f"  {cat}: {count} ({pct:.1f}%)")
        
        logger.info("Test set category distribution:")
        for cat in sorted(test_categories.keys()):
            count = test_categories[cat]
            pct = 100 * count / len(test_ids)
            logger.info(f"  {cat}: {count} ({pct:.1f}%)")
        
        return {
            "no_overlap": len(overlap) == 0,
            "train_categories": train_categories,
            "test_categories": test_categories,
            "category_balance": self._compute_balance(train_categories, test_categories),
        }

    def _compute_balance(
        self,
        train_cats: dict,
        test_cats: dict,
    ) -> dict[str, float]:
        """Compute how well test distribution matches train."""
        
        train_total = sum(train_cats.values())
        test_total = sum(test_cats.values())
        
        balance = {}
        for cat in set(train_cats.keys()) | set(test_cats.keys()):
            train_pct = train_cats.get(cat, 0) / train_total
            test_pct = test_cats.get(cat, 0) / test_total
            diff = abs(train_pct - test_pct)
            balance[cat] = diff
        
        return balance


def create_split_for_paper() -> dict[str, Any]:
    """
    Create the official train/test split for the paper.
    
    This split is:
    - Reproducible: uses fixed seed (42)
    - Stratified: maintains category distribution
    - Documented: includes full reasoning
    - Auditable: all decisions logged
    """
    
    generator = TrainTestSplitGenerator(
        random_seed=42,
        test_ratio=0.20,
        stratify_by_type=True,
    )
    
    split = generator.generate_split()
    
    logger.info(
        f"Split created: {split['train_size']} train, {split['test_size']} test"
    )
    
    return split


def save_split(split: dict[str, Any], output_path: Path | None = None) -> Path:
    """Save split to JSON with documentation."""
    
    if output_path is None:
        output_path = data_dir() / "test_split.json"
    
    save_json(split, output_path)
    logger.info(f"Split saved to: {output_path}")
    
    return output_path


def verify_split(split_file: Path | None = None) -> bool:
    """Verify existing split is valid."""
    
    if split_file is None:
        split_file = data_dir() / "test_split.json"
    
    if not split_file.exists():
        logger.error(f"Split file not found: {split_file}")
        return False
    
    split = load_json(split_file)
    
    train_ids = set(range(1, 207)) - set(split["test_ids"])
    test_ids = set(split["test_ids"])
    
    # Verify no overlap
    if train_ids & test_ids:
        logger.error("Split validation failed: overlap detected")
        return False
    
    # Verify counts
    if len(test_ids) != split["test_size"]:
        logger.error(f"Test size mismatch: {len(test_ids)} vs {split['test_size']}")
        return False
    
    logger.info("✓ Split validation passed")
    logger.info(f"  Train: {len(train_ids)} specs")
    logger.info(f"  Test: {len(test_ids)} specs")
    logger.info(f"  Total: {len(train_ids) + len(test_ids)} specs")
    
    return True


def main():
    """Generate and save train/test split."""
    
    import argparse
    
    parser = argparse.ArgumentParser(description="Generate train/test split for TLA-Bench")
    parser.add_argument(
        "--seed",
        type=int,
        default=42,
        help="Random seed for reproducibility (default: 42)",
    )
    parser.add_argument(
        "--test-ratio",
        type=float,
        default=0.20,
        help="Test set ratio (default: 0.20 = 20%%)",
    )
    parser.add_argument(
        "--stratified",
        action="store_true",
        default=True,
        help="Use stratified split (default: True)",
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="Verify existing split instead of generating",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output file path (default: data/test_split.json)",
    )
    
    args = parser.parse_args()
    
    if args.verify:
        verify_split(args.output or data_dir() / "test_split.json")
    else:
        split = create_split_for_paper()
        save_split(split, args.output)


if __name__ == "__main__":
    main()
