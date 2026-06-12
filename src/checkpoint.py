from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path

from utils import get_logger, outputs_dir

logger = get_logger("checkpoint")


class CheckpointManager:
    def __init__(self, model_id: str, base_dir: Path | None = None):
        root = Path(base_dir) if base_dir else outputs_dir() / "checkpoints"
        self.ckpt_dir = root / model_id
        self.ckpt_dir.mkdir(parents=True, exist_ok=True)

    def _path(self, spec_id: int, condition: str) -> Path:
        return self.ckpt_dir / f"{spec_id}__{condition}.json"

    def is_done(self, spec_id: int, condition: str) -> bool:
        return self._path(spec_id, condition).exists()

    def save(self, record: dict) -> None:
        # os.replace is atomic on posix, no partial writes visible to readers
        target = self._path(record["spec_id"], record["condition"])
        fd, tmp = tempfile.mkstemp(dir=self.ckpt_dir, suffix=".json.tmp")
        try:
            with os.fdopen(fd, "w") as f:
                json.dump(record, f)
            os.replace(tmp, target)
        except Exception:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise

    def load_one(self, spec_id: int, condition: str) -> dict:
        return json.loads(self._path(spec_id, condition).read_text())

    def load_all(self) -> list[dict]:
        records = []
        for f in sorted(self.ckpt_dir.glob("*.json")):
            try:
                records.append(json.loads(f.read_text()))
            except Exception as e:
                logger.warning("Skipping corrupt checkpoint %s: %s", f.name, e)
        return records

    def consolidate(self, out_path: Path) -> list[dict]:
        records = self.load_all()
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(records, indent=2))
        return records

    def clear(self) -> None:
        removed = 0
        for f in self.ckpt_dir.glob("*.json"):
            f.unlink()
            removed += 1
        if removed:
            logger.info("Cleared %d checkpoints for %s", removed, self.ckpt_dir.name)

    def count(self) -> int:
        return sum(1 for _ in self.ckpt_dir.glob("*.json"))
