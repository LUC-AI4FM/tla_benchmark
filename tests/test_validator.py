import sys
from pathlib import Path
from unittest.mock import patch

import pytest

from validator import classify_errors, validate_spec

MINIMAL_TLA = "---- MODULE Foo ----\nVARIABLES x\nInit == x = 0\nNext == x' = x + 1\n===="


def _sany(passed: bool):
    return {"passed": passed, "returncode": 0 if passed else 1, "stdout": "", "stderr": ""}


def _tlc(passed: bool):
    return {"passed": passed, "returncode": 0 if passed else 1, "stdout": "", "stderr": ""}


class TestClassifyErrors:
    def test_unicode_ops(self):
        assert classify_errors("x ∧ y")["unicode_operator_substitution"] is True

    def test_foreign_syntax_braces(self):
        assert classify_errors("{ x: 1 }")["cross_language_syntax_injection"] is True

    def test_think_tag(self):
        assert classify_errors("<think>reasoning</think>")["reasoning_formatting_leakage"] is True

    def test_missing_footer(self):
        assert classify_errors("---- MODULE Foo ----\nVARIABLES x")["structural_error_missing_footer"] is True

    def test_has_footer(self):
        assert classify_errors(MINIMAL_TLA)["structural_error_missing_footer"] is False

    def test_duplicate_module(self):
        assert classify_errors("MODULE Foo\nstuff\nMODULE Bar")["structural_error_duplicate_module"] is True

    def test_clean_spec(self):
        r = classify_errors(MINIMAL_TLA)
        assert r["unicode_operator_substitution"] is False
        assert r["cross_language_syntax_injection"] is False
        assert r["reasoning_formatting_leakage"] is False


class TestValidateSpec:
    def test_sany_pass_tlc_pass(self, tmp_path):
        tla = tmp_path / "Foo.tla"
        tla.write_text(MINIMAL_TLA)
        cfg = tmp_path / "Foo.cfg"
        cfg.write_text("INIT Init\nNEXT Next")

        with patch("validator.run_sany", return_value=_sany(True)), \
             patch("validator.run_tlc", return_value=_tlc(True)):
            result = validate_spec(str(tla), str(cfg), str(tmp_path), 1, "test_model", "nlp_to_tla")

        assert result["sany_pass"] is True
        assert result["tlc_pass"] is True

    def test_sany_fail_skips_tlc(self, tmp_path):
        tla = tmp_path / "Foo.tla"
        tla.write_text(MINIMAL_TLA)

        with patch("validator.run_sany", return_value=_sany(False)) as mock_sany, \
             patch("validator.run_tlc") as mock_tlc:
            result = validate_spec(str(tla), None, str(tmp_path), 2, "test_model", "nlp_to_tla")

        assert result["sany_pass"] is False
        assert result["tlc_pass"] is False
        mock_tlc.assert_not_called()

    def test_sany_pass_no_cfg_skips_tlc(self, tmp_path):
        tla = tmp_path / "Foo.tla"
        tla.write_text(MINIMAL_TLA)

        with patch("validator.run_sany", return_value=_sany(True)), \
             patch("validator.run_tlc") as mock_tlc:
            result = validate_spec(str(tla), None, str(tmp_path), 3, "test_model", "nlp_to_tla")

        assert result["sany_pass"] is True
        assert result["tlc_pass"] is False
        mock_tlc.assert_not_called()

    def test_result_has_required_keys(self, tmp_path):
        tla = tmp_path / "Foo.tla"
        tla.write_text(MINIMAL_TLA)

        with patch("validator.run_sany", return_value=_sany(True)):
            result = validate_spec(str(tla), None, str(tmp_path), 4, "test_model", "nlp_to_tla")

        for key in ("spec_id", "model_id", "condition", "sany_pass", "tlc_pass"):
            assert key in result

    def test_error_file_written_on_sany_fail(self, tmp_path):
        tla = tmp_path / "Foo.tla"
        tla.write_text(MINIMAL_TLA)

        with patch("validator.run_sany", return_value={
            "passed": False, "returncode": 1,
            "stdout": "unicode error ∧", "stderr": "",
        }):
            validate_spec(str(tla), None, str(tmp_path), 5, "test_model", "nlp_to_tla")

        error_file = tmp_path / "5_errors.json"
        assert error_file.exists()
