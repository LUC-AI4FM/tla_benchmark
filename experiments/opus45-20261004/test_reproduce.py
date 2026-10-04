"""Offline end-to-end evidence, correction, and tamper-detection regressions."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("paid_reproduce", HERE / "reproduce.py")
repro = importlib.util.module_from_spec(spec)
spec.loader.exec_module(repro)


class EvidenceWorkflow(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = repro.collect()
        cls.report = repro.reduce_rows(cls.rows)

    def test_complete_cli_and_frozen_report(self):
        result = subprocess.run([sys.executable, str(HERE / "reproduce.py"), "--check", "--json"],
                                text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(result.stdout), self.report)

    def test_independent_reduction_of_archived_grades(self):
        for job, summary in self.report["jobs"].items():
            grades = [json.loads(p.read_text()) for p in (HERE / "evidence" / job).rglob("author-grade.json")]
            self.assertEqual(len(grades), summary["outputs"])
            self.assertEqual(sum(g["tlc_pass"] is True for g in grades), summary["author_tlc_passes"])
            self.assertEqual(sum(g["sany_pass"] is True for g in grades), summary["author_exit_code_sany_passes"])
        independently_passing_ids = {str(json.loads(p.read_text())["spec_id"])
                                     for p in (HERE / "evidence/A3").rglob("author-grade.json")
                                     if json.loads(p.read_text())["tlc_pass"] is True}
        self.assertEqual(independently_passing_ids, set(self.report["matched_a3_pass_at_4"]["passing_ids"]))

    def test_tables_change_when_an_output_changes(self):
        changed = copy.deepcopy(self.rows)
        row = next(r for r in changed if r["job"] == "A1" and r["strict_sany"] and not r["tlc_pass"])
        row["tlc_pass"] = True
        after = repro.reduce_rows(changed)
        self.assertEqual(after["jobs"]["A1"]["author_tlc_passes"],
                         self.report["jobs"]["A1"]["author_tlc_passes"] + 1)

    def test_missing_matrix_item_is_an_error(self):
        original_load = repro.load
        def load(path):
            data = original_load(path)
            if Path(path).name == "provenance.json":
                data = copy.deepcopy(data)
                data["runs"] = [r for r in data["runs"] if r["run_id"] != "A3:1000:s1"]
            return data
        with patch.object(repro, "load", load), self.assertRaisesRegex(ValueError, "Unindexed evidence|count mismatch|Incomplete"):
            repro.collect()

    def test_request_model_mismatch_is_an_error(self):
        original_load = repro.load
        def load(path):
            data = original_load(path)
            if Path(path).name == "request.json":
                data["modelId"] = "other-model"
            return data
        with patch.object(repro, "load", load), self.assertRaisesRegex(ValueError, "Model mismatch"):
            repro.collect()

    def test_hash_missing_and_extra_file_detection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "experiment"
            root.mkdir()
            (root / "record.txt").write_text("frozen")
            protocol = {"dependencies": {}}
            (root / "protocol.json").write_text(json.dumps(protocol))
            manifest = {"files": {p.name: repro.sha(p) for p in root.iterdir()}, "repository_files": {}}
            (root / "integrity.json").write_text(json.dumps(manifest))
            repro.verify(root, Path(tmp))
            (root / "record.txt").write_text("changed")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                repro.verify(root, Path(tmp))
            (root / "record.txt").write_text("frozen")
            (root / "unexpected.txt").write_text("extra")
            with self.assertRaisesRegex(ValueError, "inventory differs"):
                repro.verify(root, Path(tmp))
            (root / "unexpected.txt").unlink()
            (root / "record.txt").unlink()
            with self.assertRaisesRegex(ValueError, "inventory differs"):
                repro.verify(root, Path(tmp))

    def test_real_semantic_error_correction_retains_author_score(self):
        directory = HERE / "evidence/A3/1000_s1"
        raw = repro.load(directory / "run_sany-raw.json")
        self.assertEqual(raw["returncode"], 0)
        self.assertTrue(repro.load(directory / "author-grade.json")["sany_pass"])
        self.assertIn("Unknown operator: `Permutations'", raw["stdout"])
        self.assertEqual(repro.strict_sany_result(raw), {"passed": False, "reason": "semantic_error"})
        # This total includes the separate smoke; the experimental total is 74.
        self.assertEqual(len(self.report["strict_parser_corrections"]), 75)
        self.assertEqual(sum(r["author_true_with_semantic_errors"] for j, r in self.report["jobs"].items()
                             if j != "smoke"), 74)

    def test_verified_timeouts_are_nonpasses(self):
        timeouts = [r for r in self.rows if r["timeout"]]
        self.assertEqual(len(timeouts), 5)
        self.assertTrue(all(r["tlc_pass"] is False for r in timeouts))
        self.assertEqual(set(self.report["timeout_ids"]),
                         {"A1:1384:s0", "A1:1610:s0", "A2:1394:s0", "A3:1394:s1", "A3:1609:s2"})

    def test_mixed_baseline_is_never_certified_pass_at_5(self):
        mixed = self.report["mixed_baseline_coverage"]
        self.assertIs(mixed["strict_pass_at_5_certified"], False)
        self.assertTrue(mixed["missing_baseline_provenance"])
        self.assertEqual(mixed["baseline_only_ids"], ["1595"])


class StrictParser(unittest.TestCase):
    def raw(self, text, code=0, stderr=""):
        return {"returncode": code, "stdout": "SANY2\nSemantic processing of module Fixture\n" + text, "stderr": stderr}

    def test_diagnostics_on_both_streams(self):
        for diagnostic in ["Semantic errors:", "*** Errors: 1", "***Parse Error***", "Lexical error", "Error: failed"]:
            for stderr in [False, True]:
                with self.subTest(diagnostic=diagnostic, stderr=stderr):
                    raw = self.raw("" if stderr else diagnostic, stderr=diagnostic if stderr else "")
                    self.assertFalse(repro.strict_sany_result(raw)["passed"])

    def test_success_warning_timeout_and_incomplete_evidence(self):
        self.assertTrue(repro.strict_sany_result(self.raw("*** Warnings: 1"))["passed"])
        self.assertFalse(repro.strict_sany_result(self.raw("", code=-1))["passed"])
        self.assertFalse(repro.strict_sany_result({"returncode": 0, "stdout": "", "stderr": ""})["passed"])
        self.assertFalse(repro.strict_sany_result(None)["passed"])
        with self.assertRaises(ValueError):
            repro.strict_sany_result({"returncode": True, "stdout": "", "stderr": ""})

    def test_real_sany_zero_exit_with_semantic_errors(self):
        java = os.environ.get("TLA_TEST_JAVA") or shutil.which("java")
        if not java:
            self.skipTest("Java unavailable; saved-evidence tests still cover the complete reduction")
        with tempfile.TemporaryDirectory() as tmp:
            fixture = Path(tmp) / "Fixture.tla"
            fixture.write_text("---- MODULE Fixture ----\nEXTENDS Naturals\nBad == MissingOperator\n====\n")
            result = subprocess.run([java, "-cp", str(repro.REPO / "tla2tools.jar"), "tla2sany.SANY", "Fixture.tla"],
                                    cwd=tmp, capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0)
            self.assertIn("Semantic errors:", result.stdout)
            self.assertFalse(repro.strict_sany_result(dict(returncode=result.returncode,
                                                          stdout=result.stdout, stderr=result.stderr))["passed"])

    def test_complete_generated_source_regrade_workflow(self):
        java = os.environ.get("TLA_TEST_JAVA") or shutil.which("java")
        if not java:
            self.skipTest("Recorded Java runtime unavailable")
        probe = subprocess.run([java, "-version"], capture_output=True, text=True, timeout=10)
        if "11.0.25+9" not in probe.stderr:
            self.skipTest("This regrade workflow requires the recorded Temurin 11.0.25+9")
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "regrade.json"
            subprocess.run([sys.executable, str(HERE / "regrade.py"), "--run-id", "A1:1343:s0",
                            "--java", str(Path(java).resolve()), "--output", str(output)],
                           capture_output=True, text=True, timeout=90, check=True)
            result = json.loads(output.read_text())
            self.assertEqual(result["new_author_protocol_grade"], {"sany_pass": True, "tlc_pass": True})
            self.assertTrue(result["new_strict_sany"]["passed"])
            self.assertIn("TLC2 Version", result["raw"]["run_tlc"]["stdout"])


if __name__ == "__main__":
    unittest.main()
