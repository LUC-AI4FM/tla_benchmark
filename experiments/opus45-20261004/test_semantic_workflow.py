"""Full independent-check reconciliation and source-grounded review packet."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import reduce_semantics as R
E = R.E


class IndependentWorkflow(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence = E.load(E.HERE / "semantic-evidence.json")
        cls.report = R.reduce_evidence(cls.evidence, allow_partial=True)

    def test_complete_cli_and_reconciliation(self):
        result = subprocess.run([sys.executable, str(E.HERE / "reduce_semantics.py"), "--allow-partial", "--check", "--json"],
                                capture_output=True, text=True, check=True)
        self.assertEqual(json.loads(result.stdout), self.report)
        passing = {r["run_id"] for r in E.collect() if r["job"] != "smoke" and r["tlc_pass"]}
        audited = {r["run_id"] for r in self.report["row_reconciliation"]}
        self.assertEqual(audited | set(self.report["unexecuted_run_ids"]), passing)
        self.assertFalse(audited & set(self.report["unexecuted_run_ids"]))
        self.assertEqual(sum(j["archived_passing_outputs_audited"] for j in self.report["jobs"].values()), len(audited))
        if not self.evidence["complete"]:
            with self.assertRaisesRegex(ValueError, "incomplete"):
                R.reduce_evidence(self.evidence)
            self.assertFalse(self.report["external_reference_qualified_a3_any_pass"]["certified_complete_audit"])
            self.assertNotIn("passing_specifications", self.report["external_reference_qualified_a3_any_pass"])

    def test_missing_check_coverage_fails_closed(self):
        data = copy.deepcopy(self.evidence)
        data["rows"].pop()
        with self.assertRaisesRegex(ValueError, "coverage differs|inventory differs"):
            R.reduce_evidence(data, allow_partial=True)

    def test_fresh_sample_alias_cannot_be_dropped(self):
        data = copy.deepcopy(self.evidence)
        fresh = next(r for r in data["rows"] if r["run_id"].startswith("A3:")
                     and r["run_id"].endswith(":s0:matched-20261004")
                     and r["execution_reused_from"] != r["run_id"])
        data["rows"].remove(fresh)
        with self.assertRaisesRegex(ValueError, "alias coverage differs"):
            R.reduce_evidence(data, allow_partial=True)

    def test_final_cohort_and_execution_inputs_are_reconciled(self):
        scope = self.report["target_scope"]
        self.assertEqual(scope["experimental_outputs"], 700)
        self.assertEqual(scope["a3_samples"], [0, 1, 2, 3, 4])
        self.assertEqual(scope["original_passing_output_rows"], 127)
        self.assertEqual(scope["original_unique_input_keys"], 114)
        self.assertEqual(scope["fresh_sample0_passing_output_rows"], 19)
        self.assertEqual(scope["fresh_sample0_new_unique_input_keys"], 13)
        self.assertEqual(scope["fresh_sample0_reused_input_keys"], 6)
        self.assertEqual(scope["passing_output_rows_by_condition"], {"A1": 22, "A2": 31, "A3": 93})
        sources = {r["run_id"]: r for r in E.collect()}
        for row in self.report["row_reconciliation"]:
            source = sources[row["run_id"]]
            self.assertEqual((row["mode"], row["description_provider"], row["sample"]),
                             (source["mode"], source["description_provider"], source["sample"]))
            self.assertEqual(row["execution_input_key"]["reference_sha256"], source["reference_sha256"])
            self.assertEqual(row["execution_input_key"]["configuration_sha256"], source["configuration_sha256"])

    def test_invented_outcome_cannot_override_raw_evidence(self):
        data = copy.deepcopy(self.evidence)
        result = next(r[c] for r in data["rows"] for c in R.COMPONENTS if r[c].get("raw") and r[c]["status"] == "holds")
        result["status"] = "violated"
        with self.assertRaisesRegex(ValueError, "raw checker logs"):
            R.reduce_evidence(data, allow_partial=True)

    def test_oracle_configuration_and_mapping_are_verified(self):
        for field in ["cfg", "mapping", "module_sha256"]:
            with self.subTest(field=field):
                data = copy.deepcopy(self.evidence)
                result = next(r["reference_properties"] for r in data["rows"] if r["reference_properties"].get("raw"))
                if field == "cfg":
                    result[field] += "\nINVARIANT TRUE\n"
                elif field == "mapping":
                    result[field]["invented"] = "binding"
                else:
                    result[field]["AuditSubject"] = "0" * 64
                with self.assertRaises(ValueError):
                    R.reduce_evidence(data, allow_partial=True)


class HumanPacket(unittest.TestCase):
    def test_rebuild_complete_unreviewed_packet_without_outputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            packet, key = Path(tmp) / "cases.jsonl", Path(tmp) / "assignments.json"
            subprocess.run([sys.executable, str(E.HERE / "build_review_cases.py"), "--output", str(packet),
                            "--private-key", str(key)], check=True, capture_output=True, text=True)
            self.assertEqual(packet.read_text(), (E.HERE / "description-review-cases.jsonl").read_text())
            rows = [json.loads(line) for line in packet.read_text().splitlines()]
            self.assertEqual(len(rows), 100)
            self.assertEqual(len({r["case_id"] for r in rows}), 100)
            assignments = E.load(key)
            self.assertEqual({r["spec_id"] for r in assignments}, {str(i) for i in E.load(E.REPO / "outputs/eval_100_ids.json")})
            for r in rows:
                self.assertEqual(r["human_review_status"], "unreviewed")
                self.assertIsNone(r["human_equivalence_assessment"])
                self.assertEqual(r["reference_sha256"], E.sha(E.REPO / r["reference_contract_path"]))
                self.assertFalse({"model_id", "provider", "generated_output", "tlc_pass"} & r.keys())


if __name__ == "__main__":
    unittest.main()
