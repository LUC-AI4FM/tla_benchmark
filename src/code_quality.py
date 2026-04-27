from __future__ import annotations

import argparse
import csv
import math
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Optional

sys.path.insert(0, str(Path(__file__).parent))

from utils import (
    data_dir, get_logger, load_json, load_text, outputs_dir,
    repo_root, results_dir, save_json,
)

logger = get_logger("code_quality")

TLA_KEYWORDS: set[str] = {
    "MODULE", "EXTENDS", "CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES",
    "ASSUME", "ASSUMPTION", "AXIOM", "THEOREM", "LEMMA", "PROPOSITION",
    "COROLLARY", "INSTANCE", "WITH", "LOCAL", "LET", "IN", "IF", "THEN",
    "ELSE", "CASE", "OTHER", "CHOOSE", "ENABLED", "UNCHANGED", "EXCEPT",
    "DOMAIN", "SUBSET", "UNION", "RECURSIVE", "LAMBDA", "NEW", "OBVIOUS",
    "OMITTED", "BY", "QED", "SUFFICES", "PICK", "HAVE", "TAKE", "WITNESS",
    "USE", "HIDE", "DEF", "DEFS", "PROOF", "PROVE",
    "TRUE", "FALSE", "BOOLEAN", "WF_", "SF_",
}

TLA_OPERATORS: set[str] = {
    "==", "\\in", "\\notin", "\\/", "/\\", "=>", "<=>",
    "~", "\\lnot", "\\neg", "\\A", "\\E",
    "[]", "<>", "~>", "'",
    "=", "#", "/=", "<", ">", "<=", ">=", "..",
    "+", "-", "*", "\\div", "%", "^",
    "\\cup", "\\cap", "\\subseteq", "\\X",
    "\\o", "\\circ", "|->", "->", ":>", "@@",
}

_OPERATOR_RE = re.compile(
    r"(?:" + "|".join(re.escape(op) for op in sorted(TLA_OPERATORS, key=len, reverse=True)) + r")"
)
_IDENTIFIER_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
_NUMBER_RE = re.compile(r"\b\d+\b")
_STRING_RE = re.compile(r'"[^"]*"')

_DECISION_PATTERNS: list[re.Pattern] = [
    re.compile(r"\bIF\b"),
    re.compile(r"\bCASE\b"),
    re.compile(r"\[\]"),
    re.compile(r"\\/"),
    re.compile(r"\\A\b"),
    re.compile(r"\\E\b"),
]


def _tokenize_tla(source: str) -> tuple[list[str], list[str]]:
    cleaned = re.sub(r"\\\*.*$", "", source, flags=re.MULTILINE)
    cleaned = re.sub(r"\(\*.*?\*\)", "", cleaned, flags=re.DOTALL)

    operators: list[str] = []
    operands: list[str] = []

    operators.extend(_OPERATOR_RE.findall(cleaned))

    for word in _IDENTIFIER_RE.findall(cleaned):
        if word in TLA_KEYWORDS:
            operators.append(word)
        else:
            operands.append(word)

    operands.extend(_NUMBER_RE.findall(cleaned))
    operands.extend(_STRING_RE.findall(cleaned))

    return operators, operands


def _ngrams(tokens: list[str], n: int) -> Counter:
    return Counter(tuple(tokens[i : i + n]) for i in range(len(tokens) - n + 1))


def _bleu_score(reference: list[str], candidate: list[str], max_n: int = 4) -> float:
    if not candidate or not reference:
        return 0.0

    brevity_penalty = min(1.0, math.exp(1 - len(reference) / max(len(candidate), 1)))
    log_avg = 0.0

    for n in range(1, max_n + 1):
        ref_ngrams = _ngrams(reference, n)
        cand_ngrams = _ngrams(candidate, n)

        clipped = sum(min(count, ref_ngrams[gram]) for gram, count in cand_ngrams.items())
        total = max(sum(cand_ngrams.values()), 1)

        precision = (clipped + 1) / (total + 1)
        log_avg += math.log(precision) / max_n

    return brevity_penalty * math.exp(log_avg)


def _keyword_match_score(reference: str, candidate: str) -> float:
    ref_kw = {w for w in _IDENTIFIER_RE.findall(reference) if w in TLA_KEYWORDS}
    cand_kw = {w for w in _IDENTIFIER_RE.findall(candidate) if w in TLA_KEYWORDS}

    if not ref_kw and not cand_kw:
        return 1.0
    if not ref_kw or not cand_kw:
        return 0.0

    common = ref_kw & cand_kw
    precision = len(common) / len(cand_kw)
    recall = len(common) / len(ref_kw)

    if precision + recall == 0:
        return 0.0
    return 2 * precision * recall / (precision + recall)


def _ast_similarity(ref_ast: dict, gen_ast: Optional[dict]) -> float:
    if gen_ast is None:
        return 0.0

    def _sim(a: Any, b: Any) -> float:
        if isinstance(a, dict) and isinstance(b, dict):
            all_keys = set(a.keys()) | set(b.keys())
            if not all_keys:
                return 1.0
            return sum(_sim(a.get(k), b.get(k)) for k in all_keys) / len(all_keys)
        elif isinstance(a, list) and isinstance(b, list):
            max_len = max(len(a), len(b))
            if max_len == 0:
                return 1.0
            return sum(
                _sim(a[i] if i < len(a) else None, b[i] if i < len(b) else None)
                for i in range(max_len)
            ) / max_len
        elif a == b:
            return 1.0
        elif a is None or b is None:
            return 0.0
        else:
            return 0.0

    return _sim(ref_ast, gen_ast)


def compute_codebleu(
    reference_tla: str,
    candidate_tla: str,
    reference_ast: Optional[dict] = None,
    candidate_ast: Optional[dict] = None,
    weights: tuple[float, float, float] = (0.35, 0.35, 0.30),
) -> dict[str, float]:
    ref_ops, ref_opnds = _tokenize_tla(reference_tla)
    cand_ops, cand_opnds = _tokenize_tla(candidate_tla)

    ref_tokens = ref_ops + ref_opnds
    cand_tokens = cand_ops + cand_opnds

    token_bleu = _bleu_score(ref_tokens, cand_tokens)
    ast_sim = _ast_similarity(reference_ast, candidate_ast) if reference_ast else 0.0
    kw_match = _keyword_match_score(reference_tla, candidate_tla)

    w_bleu, w_ast, w_kw = weights
    if reference_ast is None:
        w_bleu, w_ast, w_kw = 0.55, 0.0, 0.45

    codebleu = w_bleu * token_bleu + w_ast * ast_sim + w_kw * kw_match

    return {
        "codebleu": round(codebleu, 4),
        "token_bleu": round(token_bleu, 4),
        "ast_similarity": round(ast_sim, 4),
        "keyword_match": round(kw_match, 4),
    }


def compute_cyclomatic(source: str) -> int:
    cleaned = re.sub(r"\\\*.*$", "", source, flags=re.MULTILINE)
    cleaned = re.sub(r"\(\*.*?\*\)", "", cleaned, flags=re.DOTALL)

    decision_points = 0
    for pattern in _DECISION_PATTERNS:
        decision_points += len(pattern.findall(cleaned))

    return max(1, decision_points + 1)


def compute_halstead(source: str) -> dict[str, float]:
    operators, operands = _tokenize_tla(source)

    distinct_ops = set(operators)
    distinct_opnds = set(operands)

    eta1 = len(distinct_ops)
    eta2 = max(len(distinct_opnds), 1)
    n1 = len(operators)
    n2 = len(operands)

    vocabulary = eta1 + eta2
    length = n1 + n2
    volume = length * math.log2(max(vocabulary, 2))
    difficulty = (eta1 / 2) * (n2 / eta2)
    effort = difficulty * volume

    return {
        "eta1": eta1, "eta2": eta2, "N1": n1, "N2": n2,
        "vocabulary": vocabulary, "length": length,
        "volume": round(volume, 2),
        "difficulty": round(difficulty, 2),
        "effort": round(effort, 2),
    }


def compute_maintainability_index(
    source: str,
    halstead_volume: Optional[float] = None,
    cyclomatic: Optional[int] = None,
) -> float:
    if halstead_volume is None:
        halstead_volume = compute_halstead(source)["volume"]
    if cyclomatic is None:
        cyclomatic = compute_cyclomatic(source)

    loc = 0
    for line in source.splitlines():
        stripped = line.strip()
        if stripped and not stripped.startswith("\\*") and not stripped.startswith("(*"):
            loc += 1
    loc = max(loc, 1)

    mi = 171 - 5.2 * math.log(max(halstead_volume, 1)) - 0.23 * cyclomatic - 16.2 * math.log(loc)
    return round(max(0.0, min(171.0, mi)), 2)


def compute_all_metrics(
    candidate_tla: str,
    reference_tla: Optional[str] = None,
    reference_ast: Optional[dict] = None,
) -> dict[str, Any]:
    halstead = compute_halstead(candidate_tla)
    cyclomatic = compute_cyclomatic(candidate_tla)
    mi = compute_maintainability_index(candidate_tla, halstead["volume"], cyclomatic)

    result: dict[str, Any] = {
        "cyclomatic_complexity": cyclomatic,
        "maintainability_index": mi,
        **{f"halstead_{k}": v for k, v in halstead.items()},
    }

    if reference_tla is not None:
        codebleu = compute_codebleu(reference_tla, candidate_tla, reference_ast)
        result.update(codebleu)

    return result


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute TLA+ code quality metrics.")
    parser.add_argument("--model", default=None)
    parser.add_argument("--condition", default=None)
    args = parser.parse_args()

    extracted_base = outputs_dir() / "extracted"
    if not extracted_base.exists():
        logger.error("No extracted outputs found at %s", extracted_base)
        return

    output_dir = results_dir() / "code_quality"
    output_dir.mkdir(parents=True, exist_ok=True)

    all_rows: list[dict[str, Any]] = []

    for model_dir in sorted(extracted_base.iterdir()):
        if not model_dir.is_dir():
            continue
        model_id = model_dir.name
        if args.model and model_id != args.model:
            continue

        for cond_dir in sorted(model_dir.iterdir()):
            if not cond_dir.is_dir():
                continue
            condition = cond_dir.name
            if args.condition and condition != args.condition:
                continue

            for spec_dir in sorted(cond_dir.iterdir()):
                if not spec_dir.is_dir():
                    continue
                spec_id = spec_dir.name

                ref_tla_path = data_dir() / "tla_files" / f"{spec_id}.tla"
                reference_tla = load_text(ref_tla_path) if ref_tla_path.exists() else None

                ref_ast_path = data_dir() / "ast_json" / f"{spec_id}.json"
                reference_ast = load_json(ref_ast_path) if ref_ast_path.exists() else None

                for tla_file in sorted(spec_dir.glob("*.tla")):
                    candidate_tla = load_text(tla_file)
                    sample_name = tla_file.stem

                    metrics = compute_all_metrics(candidate_tla, reference_tla, reference_ast)

                    row = {
                        "model_id": model_id, "condition": condition,
                        "spec_id": spec_id, "sample": sample_name,
                        **metrics,
                    }
                    all_rows.append(row)

            logger.info("computed  model=%s cond=%s specs=%d", model_id, condition, len(all_rows))

    if not all_rows:
        logger.warning("No generated specifications found.")
        return

    fieldnames = list(all_rows[0].keys())
    agg_path = output_dir / "aggregate.csv"
    with open(agg_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(all_rows)

    logger.info("wrote %d rows to %s", len(all_rows), agg_path)

    from itertools import groupby

    all_rows.sort(key=lambda r: (r["model_id"], r["condition"]))
    for (mid, cond), group in groupby(all_rows, key=lambda r: (r["model_id"], r["condition"])):
        rows = list(group)
        per_path = output_dir / f"{mid}_{cond}.csv"
        with open(per_path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        logger.info("wrote %s (%d rows)", per_path.name, len(rows))


if __name__ == "__main__":
    main()
