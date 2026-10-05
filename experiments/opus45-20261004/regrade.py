#!/usr/bin/env python3
"""Regrade one saved generated source with the frozen protocol, without APIs.

Writes a new result outside the evidence directory. Historical grades are immutable.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

import reproduce as evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", required=True, help="e.g. A1:1343:s0")
    parser.add_argument("--java", required=True, help="absolute path to Temurin 11.0.25+9 java")
    parser.add_argument("--output", required=True, type=Path, help="new JSON file outside frozen evidence")
    args = parser.parse_args()
    evidence.verify()
    java = Path(args.java).resolve()
    probe = subprocess.run([str(java), "-version"], capture_output=True, text=True, timeout=10, check=True)
    evidence.require('openjdk version "11.0.25"' in probe.stderr
                     and "11.0.25+9" in probe.stderr, "Expected the recorded Temurin 11.0.25+9 runtime")
    output = args.output.resolve()
    evidence.require(not output.is_relative_to(evidence.HERE), "Choose output outside frozen experiment directory")
    evidence.require(not output.exists(), "Output already exists; choose a new path")
    rows = {r["run_id"]: r for r in evidence.collect()}
    evidence.require(args.run_id in rows, "Unknown recorded run ID")
    chain = next(c for c in evidence.load(evidence.HERE / "provenance.json")["runs"] if c["run_id"] == args.run_id)
    directory = evidence.HERE / chain["directory"]
    sys.path[:0] = [str(evidence.REPO / "code/analysis"), str(evidence.REPO / "code")]
    import grading
    import validator
    validator._find_java = lambda: str(java)
    raw = {}
    subprocess_module = validator.subprocess

    class ProcessFacade:
        def __getattr__(self, name):
            return getattr(subprocess_module, name)

        def run(self, cmd, **kwargs):
            # Match the recorded memory limits; retain the grader's commands/timeouts.
            cmd = [cmd[0], "-Xmx8g", "-XX:MaxMetaspaceSize=512m", *cmd[1:]]
            if "tlc2.TLC" not in cmd:
                return subprocess_module.run(cmd, **kwargs)
            timeout = kwargs.pop("timeout")
            kwargs.pop("capture_output")
            started = time.monotonic()
            child = subprocess_module.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **kwargs)
            try:
                out, err = child.communicate(timeout=timeout)
                return subprocess.CompletedProcess(cmd, child.returncode, out, err)
            except subprocess.TimeoutExpired:
                child.kill()
                out, err = child.communicate(timeout=10)
                evidence.require(child.poll() is not None, "TLC timeout cleanup not verified")
                raw["controlled_timeout"] = {"limit_seconds": timeout, "elapsed_seconds": time.monotonic() - started,
                                             "child_reaped": True, "child_returncode": child.returncode,
                                             "partial_stdout": out, "partial_stderr": err}
                raise subprocess.TimeoutExpired(cmd, timeout)

    validator.subprocess = ProcessFacade()
    for stage in ["run_sany", "run_tlc"]:
        original = getattr(grading, stage)
        def capture(*a, _stage=stage, _original=original, **kw):
            result = _original(*a, **kw)
            raw[_stage] = result
            return result
        setattr(grading, stage, capture)
    grade = grading.grade_clean((directory / "generation.tla").read_text(),
                                evidence.REPO / rows[args.run_id]["reference_path"])
    result = {"run_id": args.run_id, "runtime": probe.stderr.strip(), "historical_author_grade": evidence.load(directory / "author-grade.json"),
              "new_author_protocol_grade": grade, "new_strict_sany": evidence.strict_sany_result(raw.get("run_sany")),
              "raw": raw, "note": "New local checker execution; stochastic TLC outcomes can differ from frozen grades."}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"run_id": args.run_id, "author_protocol": grade, "strict_sany": result["new_strict_sany"]}))


if __name__ == "__main__":
    main()
