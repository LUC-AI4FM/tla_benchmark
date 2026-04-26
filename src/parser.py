from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Optional

sys.path.insert(0, str(Path(__file__).parent))
from utils import get_logger

logger = get_logger("parser")

_FENCE_PATTERN = re.compile(
    r"```(?:tla\+?|TLA\+?)?\s*\n(.*?)```",
    re.DOTALL | re.IGNORECASE,
)

_MODULE_PATTERN = re.compile(
    r"(-{4,}\s*MODULE\s+\w+\s*-{4,}.*?={4,})",
    re.DOTALL,
)

_THINK_PATTERN = re.compile(r"<think>.*?</think>", re.DOTALL | re.IGNORECASE)


def _strip_reasoning(text: str) -> str:
    return _THINK_PATTERN.sub("", text).strip()


def extract_tla_from_response(response: str) -> Optional[str]:
    had_think_block = bool(_THINK_PATTERN.search(response))
    cleaned = _strip_reasoning(response)

    fence_matches = _FENCE_PATTERN.findall(cleaned)
    if fence_matches:
        candidates = [m.strip() for m in fence_matches if "MODULE" in m]
        result = candidates[0] if candidates else fence_matches[0].strip()
        logger.debug(
            "Extracted via fence block (think_stripped=%s, fences=%d, with_module=%d)",
            had_think_block, len(fence_matches), len(candidates),
        )
        return result

    module_matches = _MODULE_PATTERN.findall(cleaned)
    if module_matches:
        logger.debug("Extracted via bare MODULE pattern (think_stripped=%s)", had_think_block)
        return module_matches[0].strip()

    if "MODULE" in cleaned and "====" in cleaned:
        start = cleaned.find("----")
        if start != -1:
            end = cleaned.rfind("====") + 4
            logger.debug("Extracted via raw MODULE/==== scan (think_stripped=%s)", had_think_block)
            return cleaned[start:end].strip()

    logger.warning(
        "Extraction failed: no TLA+ block found (response_len=%d, think_stripped=%s)",
        len(response), had_think_block,
    )
    return None


def merge_step_outputs(steps: list[str]) -> Optional[str]:
    logger.debug("Merging %d step outputs for final extraction", len(steps))
    combined = "\n".join(steps)
    result = extract_tla_from_response(combined)
    if result is None:
        logger.warning("merge_step_outputs: extraction failed on combined %d-step output", len(steps))
    return result
