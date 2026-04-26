from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent))

from utils import get_logger, repo_root, save_json

SANY_TIMEOUT = 60
TLC_TIMEOUT = 300

logger = get_logger("validator")


def _find_java() -> str:
    for candidate in ["java", "/usr/bin/java", "/usr/local/bin/java"]:
        try:
            result = subprocess.run(
                [candidate, "-version"],
                capture_output=True, text=True, timeout=10,
            )
            if result.returncode == 0 or "version" in (result.stderr + result.stdout):
                return candidate
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
    import shutil
    java = shutil.which("java")
    if java:
        return java
    raise EnvironmentError(
        "Java not found. Install JDK 11+ and ensure 'java' is on PATH. "
        "See https://adoptium.net for downloads."
    )


def _find_tla2tools() -> str:
    jar = repo_root() / "tla2tools.jar"
    if jar.exists():
        return str(jar)
    raise FileNotFoundError(
        "tla2tools.jar not found in repo root. "
        "Download from https://github.com/tlaplus/tlaplus/releases"
    )


def run_sany(tla_path: str) -> dict[str, Any]:
    java = _find_java()
    jar = _find_tla2tools()
    tla_file = Path(tla_path)
    cmd = [java, "-cp", jar, "tla2sany.SANY", str(tla_file.name)]
    logger.debug("SANY cmd: %s", " ".join(cmd))
    try:
        result = subprocess.run(
            cmd,
            cwd=str(tla_file.parent),
            capture_output=True,
            text=True,
            timeout=SANY_TIMEOUT,
        )
        passed = result.returncode == 0
        if not passed:
            first_error = next(
                (l for l in result.stdout.splitlines() if "error" in l.lower()), ""
            )
            logger.debug("SANY failed on %s (rc=%d): %s", tla_file.name, result.returncode, first_error)
        return {
            "passed": passed,
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
        }
    except subprocess.TimeoutExpired:
        logger.warning("SANY timed out (%ds) on %s", SANY_TIMEOUT, tla_file.name)
        return {"passed": False, "returncode": -1, "stdout": "", "stderr": "SANY timeout"}
    except Exception as exc:
        logger.error("SANY subprocess error on %s: %s", tla_file.name, exc)
        return {"passed": False, "returncode": -1, "stdout": "", "stderr": str(exc)}


def run_tlc(tla_path: str, cfg_path: str) -> dict[str, Any]:
    java = _find_java()
    jar = _find_tla2tools()
    tla_file = Path(tla_path)
    cmd = [
        java, "-cp", jar,
        "tlc2.TLC",
        "-config", str(Path(cfg_path).name),
        str(tla_file.name),
    ]
    logger.debug("TLC cmd: %s", " ".join(cmd))
    try:
        result = subprocess.run(
            cmd,
            cwd=str(tla_file.parent),
            capture_output=True,
            text=True,
            timeout=TLC_TIMEOUT,
        )
        has_error_line = any(
            line.startswith("Error:") for line in result.stdout.splitlines()
        )
        passed = result.returncode == 0 and not has_error_line
        if not passed:
            error_lines = [l for l in result.stdout.splitlines() if l.startswith("Error:")]
            logger.debug(
                "TLC failed on %s (rc=%d, error_lines=%d): %s",
                tla_file.name, result.returncode, len(error_lines),
                error_lines[0] if error_lines else "(no Error: line)",
            )
        return {
            "passed": passed,
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
        }
    except subprocess.TimeoutExpired:
        logger.warning("TLC timed out (%ds) on %s", TLC_TIMEOUT, tla_file.name)
        return {"passed": False, "returncode": -1, "stdout": "", "stderr": "TLC timeout"}
    except Exception as exc:
        logger.error("TLC subprocess error on %s: %s", tla_file.name, exc)
        return {"passed": False, "returncode": -1, "stdout": "", "stderr": str(exc)}


def validate_spec(
    tla_path: str,
    cfg_path: str | None,
    validation_out_dir: str,
    spec_id: int,
    model_id: str,
    condition: str,
) -> dict[str, Any]:
    sany_result = run_sany(tla_path)
    save_json(sany_result, os.path.join(validation_out_dir, f"{spec_id}_sany.json"))

    tlc_result: dict[str, Any] = {"passed": False, "skipped": True, "reason": "SANY failed"}
    if sany_result["passed"] and cfg_path and Path(cfg_path).exists():
        tlc_result = run_tlc(tla_path, cfg_path)
        save_json(tlc_result, os.path.join(validation_out_dir, f"{spec_id}_tlc.json"))

    summary = {
        "spec_id": spec_id,
        "model_id": model_id,
        "condition": condition,
        "sany_pass": sany_result["passed"],
        "tlc_pass": tlc_result.get("passed", False),
    }
    save_json(summary, os.path.join(validation_out_dir, f"{spec_id}_summary.json"))
    logger.info(
        "spec=%s model=%s condition=%s sany=%s tlc=%s",
        spec_id, model_id, condition, sany_result["passed"], tlc_result.get("passed", False),
    )
    if not sany_result["passed"]:
        error_cats = classify_errors(sany_result["stdout"] + sany_result["stderr"])
        save_json(error_cats, os.path.join(validation_out_dir, f"{spec_id}_errors.json"))

    return summary


_UNICODE_OPS = re.compile(r"[∧∨¬⇒⇔∀∃□◇↝]")
_FOREIGN_SYNTAX = re.compile(r"[;{}]|```")
_THINK_LEAK = re.compile(r"<think>|</think>|<\|thinking\|>")
_MISSING_FOOTER = re.compile(r"={4,}")
_DUPLICATE_MODULE = re.compile(r"MODULE.*MODULE", re.DOTALL)


def classify_errors(text: str) -> dict[str, bool]:
    return {
        "unicode_operator_substitution": bool(_UNICODE_OPS.search(text)),
        "cross_language_syntax_injection": bool(_FOREIGN_SYNTAX.search(text)),
        "reasoning_formatting_leakage": bool(_THINK_LEAK.search(text)),
        "generation_length_miscalibration": len(text) > 20000,
        "structural_error_missing_footer": not bool(_MISSING_FOOTER.search(text)),
        "structural_error_duplicate_module": bool(_DUPLICATE_MODULE.search(text)),
    }
