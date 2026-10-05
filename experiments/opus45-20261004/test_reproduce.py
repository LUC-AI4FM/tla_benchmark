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

    def test_upstream_manifest_updates_leave_frozen_workflow_valid(self):
        # Exercise every join and hash check with a different root manifest.
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            for child in repro.REPO.iterdir():
                if child.name not in {"manifest.jsonl", ".git"}:
                    (repo / child.name).symlink_to(child, target_is_directory=child.is_dir())
            updated = copy.deepcopy(list(repro.frozen_manifest().values()))
            for record in updated:
                record["desc_declarative_gpt"] = "A changed upstream description."
                record["desc_declarative_claude"] = "A newly filled upstream description."
                record["desc_intent_gpt"] = "New intent field."
                record["desc_intent_claude"] = "Another new intent field."
                record["source_repo"] = "changed/upstream"
            (repo / "manifest.jsonl").write_text("\n".join(map(json.dumps, updated)) + "\n")
            repro.verify(repo=repo)
            rows = repro.collect(repo=repo)
            self.assertEqual(repro.reduce_rows(rows, repo=repo), self.report)

    def test_frozen_manifest_byte_tampering_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "inputs").mkdir()
            shutil.copyfile(HERE / "protocol.json", root / "protocol.json")
            data = (HERE / "inputs/manifest.jsonl").read_bytes()
            (root / "inputs/manifest.jsonl").write_bytes(data + b"\n")
            with self.assertRaisesRegex(ValueError, "Frozen input manifest hash mismatch"):
                repro.frozen_manifest(root)

    def test_changed_description_cannot_match_saved_request(self):
        manifest = copy.deepcopy(repro.frozen_manifest())
        manifest["1000"]["desc_declarative_claude"] = "An unrelated description."
        with patch.object(repro, "frozen_manifest", return_value=manifest):
            with self.assertRaisesRegex(ValueError, "Frozen manifest/prompt mismatch"):
                repro.collect()

    def test_intent_fields_are_not_generation_inputs(self):
        manifest = copy.deepcopy(repro.frozen_manifest())
        for record in manifest.values():
            record["desc_intent"] = "Changed old intent field."
            record["desc_intent_gpt"] = "New GPT intent field."
            record["desc_intent_claude"] = "New Claude intent field."
        with patch.object(repro, "frozen_manifest", return_value=manifest):
            self.assertEqual(repro.collect(), self.rows)
        self.assertEqual(self.report["input_provenance"]["prompt_reconstruction_outputs"], len(self.rows))
        self.assertEqual(set(self.report["input_provenance"]["description_fields_used"]),
                         {"desc_declarative_gpt", "desc_declarative_claude"})

    def test_independent_reduction_of_archived_grades(self):
        for job, summary in self.report["jobs"].items():
            grades = [json.loads(p.read_text()) for p in (HERE / "evidence" / job).rglob("author-grade.json")]
            self.assertEqual(len(grades), summary["outputs"])
            self.assertEqual(sum(g["tlc_pass"] is True for g in grades), summary["author_tlc_passes"])
            self.assertEqual(sum(g["sany_pass"] is True for g in grades), summary["author_exit_code_sany_passes"])
        independently_passing_ids = {str(json.loads(p.read_text())["spec_id"])
                                     for p in (HERE / "evidence/A3").rglob("author-grade.json")
                                     if json.loads(p.read_text())["tlc_pass"] is True and json.loads(p.read_text())["sample"] in [1, 2, 3, 4]}
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
        self.assertEqual(sum(":matched-" not in r["run_id"] for r in self.report["strict_parser_corrections"]), 75)
        self.assertEqual(sum(r["author_sany"] and not r["sany_semantic_ok"] for r in self.rows
                             if r["job"] != "smoke" and ":matched-" not in r["run_id"]), 74)

    def test_verified_timeouts_are_nonpasses(self):
        timeouts = [r for r in self.rows if r["timeout"] and ":matched-" not in r["run_id"]]
        self.assertEqual(len(timeouts), 5)
        self.assertTrue(all(r["tlc_pass"] is False for r in timeouts))
        self.assertEqual({r for r in self.report["timeout_ids"] if ":matched-" not in r},
                         {"A1:1384:s0", "A1:1610:s0", "A2:1394:s0", "A3:1394:s1", "A3:1609:s2"})

    def test_mixed_baseline_is_never_certified_pass_at_5(self):
        mixed = self.report["mixed_baseline_coverage"]
        self.assertIs(mixed["strict_pass_at_5_certified"], False)
        self.assertTrue(mixed["missing_baseline_provenance"])
        self.assertEqual(mixed["baseline_only_ids"], ["1595"])

    def test_named_nonempty_completed_checks_are_required(self):
        directory = HERE / "evidence/A1/1399_s0"
        sany = repro.load(directory / "run_sany-raw.json")
        tlc = repro.load(directory / "run_tlc-raw.json")
        run = repro.load(directory / "run.json")
        cfg = (repro.REPO / run["reference_path"]).with_suffix(".cfg").read_text()
        self.assertTrue(repro.checked_result(sany, tlc, cfg)["passed"])
        for altered_cfg in [None, "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n"]:
            self.assertFalse(repro.checked_result(sany, tlc, altered_cfg)["passed"])
        for altered in [dict(tlc, returncode=1), dict(tlc, stdout="No error has been found\n0 distinct states found\nFinished in 1s"),
                        dict(tlc, stdout=tlc["stdout"] + "\nError: invalid configuration\n"),
                        dict(tlc, stdout="1 distinct states found\nFinished in 1s\nError: The invariant Inv is violated.")]:
            self.assertFalse(repro.checked_result(sany, altered, cfg)["passed"])
        with self.assertRaisesRegex(ValueError, "Malformed TLC"):
            repro.checked_result(sany, dict(tlc, returncode=False), cfg)
        self.assertFalse(repro.checked_result(repro.load(HERE / "evidence/A3/1000_s1/run_sany-raw.json"), tlc, cfg)["passed"])

    def test_sensitivity_keeps_explicit_denominators_and_row_reasons(self):
        strata = self.report["evaluation_strata"]
        self.assertEqual([strata[n]["specifications"] for n in ["full_primary", "with_original_configuration",
            "without_missing_cfg_or_single_state_fixtures"]], [100, 99, 93])
        for name, item in strata.items():
            for job in ["A1", "A2", "A3"]:
                n = len(self.report["jobs"][job]["per_sample_tlc_passes"])
                self.assertEqual(item["jobs"][job]["outputs"], item["specifications"] * n)
        self.assertEqual(len(self.report["row_reconciliation"]), len(self.rows))
        self.assertTrue(all(r["qualification_reasons"] for r in self.report["row_reconciliation"]
                            if not r["qualified_checked_tlc_pass"]))

    def test_default_description_comparison_uses_same_tasks(self):
        comparison = self.report["paired_default_description_comparison"]
        self.assertEqual(comparison["common_task_count"], 100)
        self.assertEqual(sum(r["tasks"] for r in comparison["repository_sensitivity"].values()), 100)
        a2 = {r["spec_id"]: r["tlc_pass"] for r in self.rows if r["job"] == "A2"}
        a3 = {sid: [r["tlc_pass"] for r in self.rows if r["job"] == "A3" and r["spec_id"] == sid and r["sample"] in [1, 2, 3, 4]] for sid in a2}
        for r in comparison["rows"]:
            self.assertEqual(r["paired_difference"], float(a2[r["spec_id"]]) - sum(a3[r["spec_id"]]) / len(a3[r["spec_id"]]))

    def test_matched_fifth_sample_is_fresh_and_complete(self):
        fresh = [r for r in self.rows if r["job"] == "A3" and r["sample"] == 0]
        self.assertEqual(len(fresh), 100)
        self.assertTrue(all(r["run_id"].endswith(":matched-20261004") for r in fresh))
        actual = {r["spec_id"] for r in self.rows if r["job"] == "A3" and r["tlc_pass"]}
        self.assertEqual(set(self.report["matched_a3_pass_at_5"]["passing_ids"]), actual)
        self.assertEqual(len(self.rows), 701)
        original_load = repro.load
        def tamper(path):
            data = original_load(path)
            if Path(path).name == "protocol.json":
                data.pop("additional_cohorts")
            return data
        with patch.object(repro, "load", tamper), self.assertRaisesRegex(ValueError, "Malformed run identity|Incomplete"):
            repro.collect()


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
