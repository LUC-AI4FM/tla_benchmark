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


def load_specs_from_consolidated_json():
    """Load all specifications from the new consolidated JSON files.
    
    Returns:
        dict: Mapping of spec_id to extracted spec data
    """
    spec_data = {}
    base_file = data_dir() / "TLA_Bench_BASE_Version.json"
    
    if not base_file.exists():
        logger = get_logger("utils")
        logger.warning("Consolidated BASE JSON not found at %s", base_file)
        return spec_data
    
    data = load_json(base_file)
    records = data.get("records", [])
    
    for record in records:
        spec_id = record.get("id")
        if spec_id is not None:
            spec_data[spec_id] = record
    
    return spec_data


def get_spec_by_id(spec_id):
    """Get a single specification by ID from consolidated JSON.
    
    Args:
        spec_id: The specification ID
        
    Returns:
        dict: Specification data or None if not found
    """
    base_file = data_dir() / "TLA_Bench_BASE_Version.json"
    
    if not base_file.exists():
        return None
    
    data = load_json(base_file)
    records = data.get("records", [])
    
    for record in records:
        if record.get("id") == spec_id:
            return record
    
    return None


def load_description_by_index(index):
    """Load description from consolidated description JSON by list index.
    
    Args:
        index: Index in the TLA_Description.json list
        
    Returns:
        dict: Description data or None if not found
    """
    desc_file = data_dir() / "TLA_Description.json"
    
    if not desc_file.exists():
        return None
    
    data = load_json(desc_file)
    
    if isinstance(data, list) and 0 <= index < len(data):
        return data[index].get("description") if isinstance(data[index], dict) else None
    
    return None



def get_ast_spec_by_id(spec_id):
    """Get a single specification AST by ID from consolidated AST JSON.
    
    Args:
        spec_id: The specification ID
        
    Returns:
        dict: AST specification data or None if not found
    """
    ast_file = data_dir() / "TLA_Bench_AST_Version.json"
    
    if not ast_file.exists():
        return None
    
    data = load_json(ast_file)
    records = data.get("records", [])
    
    for record in records:
        if record.get("id") == spec_id:
            return record
    
    return None

