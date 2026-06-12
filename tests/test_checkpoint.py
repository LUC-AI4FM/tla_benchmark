import json
import tempfile
from pathlib import Path

import pytest

from checkpoint import CheckpointManager


@pytest.fixture
def ckpt(tmp_path):
    return CheckpointManager("test_model", base_dir=tmp_path)


def _rec(spec_id=1, condition="nlp_to_tla", sany=True, tlc=False):
    return {
        "spec_id": spec_id,
        "condition": condition,
        "sany_pass": sany,
        "tlc_pass": tlc,
        "pass_at_1": sany and tlc,
    }


def test_not_done_initially(ckpt):
    assert not ckpt.is_done(1, "nlp_to_tla")


def test_save_and_is_done(ckpt):
    ckpt.save(_rec(spec_id=1))
    assert ckpt.is_done(1, "nlp_to_tla")


def test_save_and_load_one(ckpt):
    r = _rec(spec_id=5, sany=True, tlc=True)
    ckpt.save(r)
    loaded = ckpt.load_one(5, "nlp_to_tla")
    assert loaded["sany_pass"] is True
    assert loaded["tlc_pass"] is True


def test_load_all_empty(ckpt):
    assert ckpt.load_all() == []


def test_load_all_multiple(ckpt):
    for i in range(3):
        ckpt.save(_rec(spec_id=i))
    assert len(ckpt.load_all()) == 3


def test_different_conditions_independent(ckpt):
    ckpt.save(_rec(spec_id=1, condition="nlp_to_tla"))
    assert not ckpt.is_done(1, "v2_to_tla")
    assert ckpt.is_done(1, "nlp_to_tla")


def test_clear_removes_all(ckpt):
    for i in range(3):
        ckpt.save(_rec(spec_id=i))
    ckpt.clear()
    assert ckpt.load_all() == []
    assert ckpt.count() == 0


def test_count(ckpt):
    assert ckpt.count() == 0
    ckpt.save(_rec(spec_id=1))
    ckpt.save(_rec(spec_id=2))
    assert ckpt.count() == 2


def test_atomic_write_produces_valid_json(ckpt):
    r = _rec(spec_id=42, sany=True, tlc=True)
    ckpt.save(r)
    loaded = ckpt.load_one(42, "nlp_to_tla")
    assert loaded is not None
    assert loaded["spec_id"] == 42


def test_overwrite_existing(ckpt):
    ckpt.save(_rec(spec_id=1, sany=False))
    ckpt.save(_rec(spec_id=1, sany=True))
    loaded = ckpt.load_one(1, "nlp_to_tla")
    assert loaded["sany_pass"] is True
