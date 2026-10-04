"""Diagnostic-aware SANY verdicts, separate from archived exit-code verdicts.

SANY can exit zero after reporting semantic errors. Never overwrite an archived
grade with this interpretation; retain both and identify their definitions.
"""
from __future__ import annotations

import re


def strict_sany_result(raw: dict | None) -> dict:
    """Require a completed SANY run without parse/semantic error diagnostics."""
    if not isinstance(raw, dict):
        return {"passed": False, "reason": "missing_evidence"}
    if (type(raw.get("returncode")) is not int
            or not isinstance(raw.get("stdout"), str)
            or not isinstance(raw.get("stderr"), str)):
        raise ValueError("Malformed SANY evidence")
    text = raw["stdout"] + "\n" + raw["stderr"]
    if raw["returncode"] != 0:
        return {"passed": False, "reason": "nonzero_exit"}
    if re.search(r"semantic errors?\s*:", text, re.I):
        return {"passed": False, "reason": "semantic_error"}
    if re.search(r"\*{3}\s*Errors:\s*[1-9]\d*|parse\s*error|parseexception|"
                 r"lexical\s*error|fatal\s*errors?|^\s*Error:", text, re.I | re.M):
        return {"passed": False, "reason": "parse_or_other_error"}
    if "SANY" not in text or "Semantic processing of module" not in text:
        return {"passed": False, "reason": "incomplete_evidence"}
    return {"passed": True, "reason": "passed"}


def run_sany_strict(*args, **kwargs) -> dict:
    """Opt-in live diagnostic-aware parser; leave the historical grader intact."""
    from pathlib import Path
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from validator import run_sany
    raw = run_sany(*args, **kwargs)
    strict = strict_sany_result(raw)
    return dict(raw, author_passed=raw["passed"], passed=strict["passed"],
                strict_reason=strict["reason"])
