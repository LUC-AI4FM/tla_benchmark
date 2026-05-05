from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger

logger = get_logger("metrics")


def cyclomatic_complexity(code: str) -> float:
    decision_points = 0
    for keyword in ["IF", "ELSE", "CASE", "\\A", "\\E", "CHOOSE"]:
        decision_points += code.upper().count(keyword)
    
    nested_depth = 0
    max_depth = 0
    for char in code:
        if char in "([{":
            nested_depth += 1
            max_depth = max(max_depth, nested_depth)
        elif char in ")]}":
            nested_depth -= 1
    
    return 1 + decision_points + max(0, max_depth - 1)


def halstead_metrics(code: str) -> dict[str, float]:
    operators = {"+", "-", "*", "/", "=", "<", ">", "<=", ">=", "/=", "EXCEPT", ":", "~>", "=>", "[]", "<>"}
    
    operator_tokens = []
    operand_tokens = []
    
    tokens = code.split()
    for token in tokens:
        if any(op in token for op in operators):
            operator_tokens.append(token)
        elif token and not token.isspace():
            operand_tokens.append(token)
    
    n1 = len(operator_tokens)
    n2 = len(operand_tokens)
    N1 = len(set(operator_tokens))
    N2 = len(set(operand_tokens))
    
    if N1 == 0 or N2 == 0:
        return {
            "n1": n1,
            "n2": n2,
            "N1": N1,
            "N2": N2,
            "vocabulary": N1 + N2,
            "length": n1 + n2,
            "difficulty": 0.0,
            "effort": 0.0,
            "time_minutes": 0.0,
            "bugs": 0.0,
        }
    
    vocabulary = N1 + N2
    length = n1 + n2
    difficulty = (N1 / 2) * (n2 / N2) if N2 > 0 else 0
    effort = difficulty * length if length > 0 else 0
    time_minutes = effort / 18.0 if effort > 0 else 0
    bugs = effort ** (2/3) / 3000 if effort > 0 else 0
    
    return {
        "n1": n1,
        "n2": n2,
        "N1": N1,
        "N2": N2,
        "vocabulary": vocabulary,
        "length": length,
        "difficulty": round(difficulty, 2),
        "effort": round(effort, 2),
        "time_minutes": round(time_minutes, 2),
        "bugs": round(bugs, 4),
    }


def maintainability_index(
    cyclomatic_complexity_score: float,
    halstead_effort: float,
    lines_of_code: int,
) -> float:
    if lines_of_code == 0:
        return 0.0
    
    volume = lines_of_code * math.log2(max(1, halstead_effort))
    mi = 171 - 5.2 * math.log(max(1, volume)) - 0.23 * cyclomatic_complexity_score - 16.2 * math.log(max(1, lines_of_code))
    
    return max(0.0, min(100.0, mi))


def codebleu_ast_similarity(
    generated_ast: dict[str, Any],
    reference_ast: dict[str, Any],
) -> float:
    def flatten_ast(node: dict | list, depth: int = 0) -> list[tuple[str, int]]:
        tokens = []
        if isinstance(node, dict):
            for key, value in node.items():
                tokens.append((key, depth))
                tokens.extend(flatten_ast(value, depth + 1))
        elif isinstance(node, list):
            for item in node:
                tokens.extend(flatten_ast(item, depth))
        elif isinstance(node, str):
            tokens.append((node, depth))
        return tokens
    
    gen_tokens = flatten_ast(generated_ast)
    ref_tokens = flatten_ast(reference_ast)
    
    if not ref_tokens:
        return 1.0 if not gen_tokens else 0.0
    
    gen_set = set(gen_tokens)
    ref_set = set(ref_tokens)
    
    intersection = len(gen_set & ref_set)
    union = len(gen_set | ref_set)
    
    if union == 0:
        return 0.0
    
    return intersection / union


def syntax_match_score(generated: str, reference: str) -> float:
    gen_lines = [l.strip() for l in generated.split("\n") if l.strip()]
    ref_lines = [l.strip() for l in reference.split("\n") if l.strip()]
    
    if not ref_lines:
        return 1.0 if not gen_lines else 0.0
    
    matching_lines = sum(1 for line in gen_lines if line in ref_lines)
    
    return matching_lines / len(ref_lines)


def compute_code_quality_metrics(
    generated_code: str,
    reference_code: str | None = None,
) -> dict[str, Any]:
    lines_of_code = len([l for l in generated_code.split("\n") if l.strip()])
    cc = cyclomatic_complexity(generated_code)
    halstead = halstead_metrics(generated_code)
    mi = maintainability_index(cc, halstead["effort"], lines_of_code)
    
    metrics = {
        "lines_of_code": lines_of_code,
        "cyclomatic_complexity": round(cc, 2),
        "halstead": halstead,
        "maintainability_index": round(mi, 2),
    }
    
    if reference_code:
        syntax_score = syntax_match_score(generated_code, reference_code)
        metrics["syntax_match_score"] = round(syntax_score, 4)
    
    return metrics


def extract_ast(code: str) -> dict[str, Any]:
    lines = [l.strip() for l in code.split("\n") if l.strip()]
    
    ast = {
        "type": "module",
        "children": [],
    }
    
    current_section = None
    for line in lines:
        if line.startswith("----"):
            current_section = "operator"
            ast["children"].append({
                "type": current_section,
                "name": line.replace("-", "").strip(),
                "content": line,
            })
        elif line.startswith("===="):
            current_section = "end"
        elif "==" in line:
            parts = line.split("==", 1)
            ast["children"].append({
                "type": "definition",
                "name": parts[0].strip(),
                "value": parts[1].strip() if len(parts) > 1 else "",
            })
        elif any(kw in line for kw in ["MODULE", "VARIABLE", "CONSTANT", "ASSUME"]):
            ast["children"].append({
                "type": line.split()[0].lower(),
                "content": line,
            })
    
    return ast


def compare_code_quality(
    generated_code: str,
    reference_code: str,
) -> dict[str, Any]:
    gen_metrics = compute_code_quality_metrics(generated_code, reference_code)
    ref_metrics = compute_code_quality_metrics(reference_code)

    comparison = {
        "generated": gen_metrics,
        "reference": ref_metrics,
        "deltas": {
            "lines_of_code": gen_metrics["lines_of_code"] - ref_metrics["lines_of_code"],
            "cyclomatic_complexity": gen_metrics["cyclomatic_complexity"] - ref_metrics["cyclomatic_complexity"],
            "maintainability_index": gen_metrics["maintainability_index"] - ref_metrics["maintainability_index"],
        },
    }

    return comparison


# ---------------------------------------------------------------------------
# Convenience wrappers used by dpo_model_tester and other callers
# ---------------------------------------------------------------------------

def compute_cyclomatic_complexity(code: str) -> float:
    return cyclomatic_complexity(code)


def compute_halstead_metrics(code: str) -> dict[str, float]:
    return halstead_metrics(code)


def compute_maintainability_index(code: str) -> float:
    lines_of_code = len([l for l in code.split("\n") if l.strip()])
    cc = cyclomatic_complexity(code)
    h = halstead_metrics(code)
    return maintainability_index(cc, h["effort"], lines_of_code)


def compute_codebleu(generated_code: str, reference_ast: dict[str, Any], spec_id: int) -> float:
    """Compute AST-based similarity between generated code and a reference AST."""
    gen_ast = extract_ast(generated_code)
    return codebleu_ast_similarity(gen_ast, reference_ast)
