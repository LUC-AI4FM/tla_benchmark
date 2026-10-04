"""Real evaluator controls: check relaxation, independent kills, fail-closed errors."""
import os
from pathlib import Path
import re
import shutil
import subprocess
import unittest
from unittest.mock import patch

import semantic_audit as A

REFERENCE = r"""---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x < 2 THEN x + 1 ELSE 0
Spec == Init /\ [][Next]_x
Inv == x \in 0..2
====
"""
CFG = "SPECIFICATION Spec\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n"


def graph_behavior(graph):
    """State labels and transitions, independent of GraphViz formatting."""
    nodes = set(re.findall(r'(-?\d+) \[label="([^"]*)"', graph))
    edges = set(re.findall(r'(-?\d+) -> (-?\d+)', graph))
    return nodes, edges


class ClassifierRegressions(unittest.TestCase):
    def test_actual_zero_exit_semantic_error_log(self):
        s = A.E.load(A.E.HERE / "evidence/A3/1000_s1/run_sany-raw.json")
        result = A.verdict(s, None)
        self.assertEqual(result["status"], "sany_rejected")
        self.assertFalse(result["sany_semantic_ok"])
        self.assertFalse(result["semantic_kill"])

    def test_actual_timeout_is_not_a_semantic_kill(self):
        directory = A.E.HERE / "evidence/A1/1384_s0"
        result = A.verdict(A.E.load(directory / "run_sany-raw.json"),
                           A.E.load(directory / "run_tlc-raw.json"), timeout=True)
        self.assertEqual(result["status"], "timeout")
        self.assertFalse(result["semantic_kill"])

    def test_incomplete_checker_result_fails_closed(self):
        s = {"returncode": 0, "stdout": "SANY2\nSemantic processing of module Counter", "stderr": ""}
        t = {"returncode": 0, "stdout": "No error has been found\n0 distinct states found", "stderr": ""}
        self.assertEqual(A.verdict(s, t)["status"], "incomplete_or_empty_model")
        with self.assertRaises(ValueError):
            A.verdict({"returncode": None, "stdout": "", "stderr": ""}, None)
        with self.assertRaisesRegex(ValueError, "Malformed TLC"):
            A.verdict(s, dict(t, returncode=False))
        contradictory = dict(t, stdout="No error has been found\n1 distinct states found\nFinished in 1s\nError: invalid configuration")
        self.assertEqual(A.verdict(s, contradictory)["status"], "checker_diagnostic_error")

    def test_mapping_is_explicit_and_not_inferred(self):
        target = REFERENCE.replace("VARIABLE x", "VARIABLE y")
        result = A.oracle_wrapper(target, REFERENCE, CFG, "properties")
        self.assertEqual(result["status"], "unresolved_mapping")


class LiveEvaluatorControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.java = os.environ.get("TLA_TEST_JAVA") or shutil.which("java")
        if not cls.java:
            raise unittest.SkipTest("Java unavailable")
        cls.origin = A.E.REPO / "specs/gold"

    def run_original_check(self, text, cfg=CFG, graph=False):
        plan = {"status": "ready", "modules": {"Counter": text}, "primary": "Counter", "cfg": cfg}
        return A.execute(plan, self.origin, self.java, timeout=30, dump_graph=graph)

    def test_true_and_removed_check_preserve_passing_behavior(self):
        base = self.run_original_check(REFERENCE, graph=True)
        relaxed = self.run_original_check(REFERENCE.replace("Inv == x \\in 0..2", "Inv == TRUE"), graph=True)
        removed = self.run_original_check(REFERENCE, A.cfg_without_checks(CFG), graph=True)
        for result in [base, relaxed, removed]:
            self.assertEqual(result["status"], "holds", result)
            self.assertTrue(result["nonempty_init"])
        self.assertTrue(graph_behavior(base["graph"])[0])
        self.assertTrue(graph_behavior(base["graph"])[1])
        self.assertEqual(graph_behavior(base["graph"]), graph_behavior(relaxed["graph"]))
        self.assertEqual(graph_behavior(base["graph"]), graph_behavior(removed["graph"]))

    def test_false_is_rejected_on_a_nonempty_model(self):
        base = self.run_original_check(REFERENCE)
        self.assertTrue(base["nonempty_init"])
        result = self.run_original_check(REFERENCE.replace("Inv == x \\in 0..2", "Inv == FALSE"))
        self.assertEqual(result["status"], "false_check_rejected", result)
        self.assertFalse(result["semantic_kill"])

    def test_frozen_external_check_rejects_requirement_breaking_transition(self):
        mutant = REFERENCE.replace("Next == x' = IF x < 2 THEN x + 1 ELSE 0", "Next == x' = -1")
        # A candidate-side tautology cannot weaken the separate frozen oracle.
        mutant = mutant.replace("Inv == x \\in 0..2", "Inv == TRUE")
        control = A.execute(A.oracle_wrapper(REFERENCE, REFERENCE, CFG, "properties"), self.origin, self.java, 30)
        killed = A.execute(A.oracle_wrapper(mutant, REFERENCE, CFG, "properties"), self.origin, self.java, 30)
        self.assertEqual(control["status"], "holds", control)
        self.assertEqual(killed["status"], "violated", killed)
        self.assertTrue(killed["semantic_kill"])
        self.assertEqual(killed["mapping"], {"x": "x"})

    def test_missing_required_behavior_is_detected_by_reverse_refinement(self):
        disabled = REFERENCE.replace("Next == x' = IF x < 2 THEN x + 1 ELSE 0", "Next == UNCHANGED x")
        forward = A.execute(A.oracle_wrapper(disabled, REFERENCE, CFG, "behavior"), self.origin, self.java, 30)
        reverse = A.execute(A.oracle_wrapper(REFERENCE, disabled, CFG, "behavior"), self.origin, self.java, 30)
        self.assertEqual(forward["status"], "holds", forward)
        self.assertEqual(reverse["status"], "violated", reverse)

    def test_invalid_transition_is_not_a_semantic_kill(self):
        invalid = REFERENCE.replace("Next == x' = IF x < 2 THEN x + 1 ELSE 0", "Next == x' = UnknownOperator")
        result = A.execute(A.oracle_wrapper(invalid, REFERENCE, CFG, "properties"), self.origin, self.java, 30)
        self.assertEqual(result["status"], "sany_rejected", result)
        self.assertFalse(result["semantic_kill"])


if __name__ == "__main__":
    unittest.main()
