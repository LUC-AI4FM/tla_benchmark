from __future__ import annotations

import json
import logging
import os
import time
from pathlib import Path
from typing import Any


def load_json(path: str | Path) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def save_json(data: Any, path: str | Path) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def save_text(text: str, path: str | Path) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def load_text(path: str | Path) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


_LOG_FORMAT = "%(asctime)s %(levelname)s %(name)s: %(message)s"
_root_configured = False


def _configure_root_logger() -> None:
    global _root_configured
    if _root_configured:
        return
    _root_configured = True

    log_dir = Path(__file__).parent.parent / "outputs" / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    log_file = log_dir / "run.log"

    formatter = logging.Formatter(_LOG_FORMAT)

    file_handler = logging.FileHandler(log_file, encoding="utf-8")
    file_handler.setFormatter(formatter)

    console_handler = logging.StreamHandler()
    console_handler.setFormatter(formatter)

    root = logging.getLogger()
    if not root.handlers:
        root.addHandler(file_handler)
        root.addHandler(console_handler)
        root.setLevel(logging.INFO)
    else:
        root.addHandler(file_handler)


def get_logger(name: str) -> logging.Logger:
    _configure_root_logger()
    return logging.getLogger(name)


def retry_with_backoff(func, max_attempts: int = 5, base_delay: float = 1.0):
    logger = get_logger("retry")
    for attempt in range(max_attempts):
        try:
            return func()
        except Exception as exc:
            if attempt == max_attempts - 1:
                raise
            delay = base_delay * (2 ** attempt)
            logger.warning("Attempt %d failed: %s. Retrying in %.1fs", attempt + 1, exc, delay)
            time.sleep(delay)


def repo_root() -> Path:
    return Path(__file__).parent.parent


def data_dir() -> Path:
    return repo_root() / "data"


def outputs_dir() -> Path:
    return repo_root() / "outputs"


def results_dir() -> Path:
    return repo_root() / "results"


# module level cache built once on first access, O(1) lookups
_spec_cache: dict[int, dict] | None = None


def _build_spec_cache() -> dict[int, dict]:
    global _spec_cache
    if _spec_cache is not None:
        return _spec_cache
    index_file = data_dir() / "index.json"
    if not index_file.exists():
        _spec_cache = {}
        return _spec_cache
    raw = load_json(index_file)
    _spec_cache = {int(k): v for k, v in raw.items()}
    return _spec_cache


def get_spec_by_id(spec_id: int) -> dict | None:
    return _build_spec_cache().get(spec_id)


def get_tla_path(spec_id: int) -> Path | None:
    entry = get_spec_by_id(spec_id)
    if entry is None:
        return None
    p = repo_root() / entry["tla_path"]
    return p if p.exists() else None

