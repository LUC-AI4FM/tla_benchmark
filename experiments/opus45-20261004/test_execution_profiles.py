"""Real qualified-runtime continuation preserves frozen completed checker evidence."""
import copy
import os
from pathlib import Path
import shutil
import tempfile
import unittest

import continue_reference_audit as C
E = C.E


class ExecutionProfiles(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.java = os.environ.get("TLA_TEST_JAVA") or shutil.which("java")
        if not cls.java:
            raise unittest.SkipTest("Java unavailable")
        cls.profile = C.qualify(str(Path(cls.java).resolve()))

    def test_live_receipt_rejects_changed_limits_and_invented_controls(self):
        C.validate_profile(self.profile)
        for mutation in ["limits", "control", "build"]:
            with self.subTest(mutation=mutation):
                p = copy.deepcopy(self.profile)
                if mutation == "limits":
                    p["limits"]["TLC_seconds"] = 6
                elif mutation == "control":
                    p["controls"]["broken_transition"]["status"] = "holds"
                else:
                    p["runtime"]["java_build"] = "17.0.12"
                p["profile_id"] = C.digest({k: v for k, v in p.items() if k != "profile_id"})
                with self.assertRaises(ValueError):
                    C.validate_profile(p)

    def test_missing_profile_receipt_fails_closed(self):
        import reduce_semantics as R
        evidence = copy.deepcopy(E.load(E.HERE / "semantic-evidence.json"))
        evidence["rows"][0]["execution_profile_id"] = "unrecorded-runtime"
        with self.assertRaisesRegex(ValueError, "Missing execution profile"):
            R.reduce_evidence(evidence, allow_partial=True)

    def test_real_bounded_continuation_preserves_completed_records(self):
        import reduce_semantics as R
        evidence = copy.deepcopy(E.load(E.HERE / "semantic-evidence.json"))
        if evidence["complete"]:
            protected = {r["reference_self_check_execution"]["reused_from_run_id"] for r in evidence["rows"]
                         if r.get("reference_self_check_execution")}
            source = next(r for r in evidence["rows"] if r["execution_reused_from"] not in protected)
            group = (source["generated_sha256"], source["reference_sha256"], source["original_configuration_sha256"])
            evidence["rows"] = [r for r in evidence["rows"] if
                (r["generated_sha256"], r["reference_sha256"], r["original_configuration_sha256"]) != group]
            evidence["complete"] = False
            evidence["completed_unique_outputs"] -= 1
        before = {r["run_id"]: copy.deepcopy(r) for r in evidence["rows"]}
        completed = evidence["completed_unique_outputs"]
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "checkpoint.json"
            C.continue_checks(evidence, self.profile, str(Path(self.java).resolve()), 1, output)
            resumed = E.load(output)
            self.assertEqual(resumed["completed_unique_outputs"], completed + 1)
            observed = {r["run_id"]: r for r in resumed["rows"]}
            self.assertTrue(set(before) < set(observed))
            self.assertTrue(all(observed[rid] == row for rid, row in before.items()))
            report = R.reduce_evidence(resumed, allow_partial=True)
            self.assertFalse(report["external_reference_qualified_a3_any_pass"]["certified_complete_audit"])
            self.assertIn(self.profile["profile_id"], report["execution_profile_output_counts"])


if __name__ == "__main__":
    unittest.main()
