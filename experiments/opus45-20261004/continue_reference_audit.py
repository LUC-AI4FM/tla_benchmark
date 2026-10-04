#!/usr/bin/env python3
"""Resume frozen reference checks with a separately qualified execution profile."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess

import semantic_audit as A
import test_semantic_audit as T
E = A.E
LEGACY_PROFILE = "original-mac-temurin11"
ALLOWED_BUILDS = {"11.0.25+9", "25.0.3+9-LTS"}
LIMITS = {"audit_workers": 1, "TLC_workers": 1, "SANY_seconds": 60,
          "TLC_seconds": 5, "heap_MiB": 512, "seed": 1, "fingerprint": 0}


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def runtime(java):
    probe = subprocess.run([java, "-version"], capture_output=True, text=True, check=True, timeout=10)
    build = re.search(r"\(build ([^\s)]+)", probe.stderr)
    E.require(build is not None and build[1] in ALLOWED_BUILDS, "Unqualified Java build")
    return {"java_version_output": probe.stderr.strip(), "java_build": build[1],
            "java_binary_sha256": E.sha(Path(java).resolve()),
            "system": platform.system(), "kernel": platform.release(), "architecture": platform.machine(),
            "python_version": platform.python_version(),
            "cpu_affinity": sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None}


def control_plans():
    original = {"status": "ready", "modules": {"Counter": T.REFERENCE}, "primary": "Counter", "cfg": T.CFG,
                "config_kind": "derived_control"}
    tautology = T.REFERENCE.replace("Inv == x \\in 0..2", "Inv == TRUE")
    broken = T.REFERENCE.replace("Next == x' = IF x < 2 THEN x + 1 ELSE 0", "Next == x' = -1")
    disabled = T.REFERENCE.replace("Next == x' = IF x < 2 THEN x + 1 ELSE 0", "Next == UNCHANGED x")
    invalid = T.REFERENCE.replace("Next == x' = IF x < 2 THEN x + 1 ELSE 0", "Next == x' = UnknownOperator")
    return {
        "base": original,
        "tautology": dict(original, modules={"Counter": tautology}),
        "removed": dict(original, cfg=A.cfg_without_checks(T.CFG)),
        "false": dict(original, modules={"Counter": T.REFERENCE.replace("Inv == x \\in 0..2", "Inv == FALSE")}),
        "external_control": A.oracle_wrapper(T.REFERENCE, T.REFERENCE, T.CFG, "properties"),
        "broken_transition": A.oracle_wrapper(broken.replace("Inv == x \\in 0..2", "Inv == TRUE"), T.REFERENCE, T.CFG, "properties"),
        "disabled_forward": A.oracle_wrapper(disabled, T.REFERENCE, T.CFG, "behavior"),
        "disabled_reverse": A.oracle_wrapper(T.REFERENCE, disabled, T.CFG, "behavior"),
        "invalid_transition": A.oracle_wrapper(invalid, T.REFERENCE, T.CFG, "properties"),
    }


def validate_profile(profile):
    import reduce_semantics as R
    E.require(profile["runtime"]["java_build"] in ALLOWED_BUILDS, "Unqualified Java build")
    E.require(profile["limits"] == LIMITS, "Execution profile changed checker limits")
    E.require(profile["evaluator_sha256"] == E.sha(E.HERE / "semantic_audit.py")
              and profile["continuation_sha256"] == E.sha(Path(__file__))
              and profile["checker_sha256"] == E.sha(E.REPO / "tla2tools.jar")
              and profile["control_source_sha256"] == E.sha(E.HERE / "test_semantic_audit.py"),
              "Execution profile code/checker differs")
    controls = profile["controls"]
    plans = control_plans()
    E.require(set(controls) == set(plans), "Incomplete runtime qualification controls")
    expected = {"base": "holds", "tautology": "holds", "removed": "holds", "false": "false_check_rejected",
                "external_control": "holds", "broken_transition": "violated", "disabled_forward": "holds",
                "disabled_reverse": "violated", "invalid_transition": "sany_rejected"}
    for name, plan in plans.items():
        R.verify_execution(controls[name], plan, E.REPO / "specs/gold")
        E.require(controls[name]["status"] == expected[name], f"Runtime control failed: {name}")
    graph = T.graph_behavior(controls["base"]["graph"])
    E.require(bool(graph[0]) and bool(graph[1]) and graph == T.graph_behavior(controls["tautology"]["graph"])
              == T.graph_behavior(controls["removed"]["graph"]), "Relaxed checks changed controlled behavior")
    E.require(controls["base"]["nonempty_init"] and controls["broken_transition"]["semantic_kill"]
              and controls["disabled_reverse"]["semantic_kill"] and not controls["false"]["semantic_kill"]
              and not controls["invalid_transition"]["semantic_kill"], "Runtime fail-closed controls differ")
    payload = {k: v for k, v in profile.items() if k != "profile_id"}
    E.require(profile["profile_id"] == digest(payload), "Execution profile receipt hash differs")


def qualify(java):
    profile = {"schema": 1, "runtime": runtime(java), "limits": LIMITS,
               "evaluator_sha256": E.sha(E.HERE / "semantic_audit.py"), "continuation_sha256": E.sha(Path(__file__)),
               "checker_sha256": E.sha(E.REPO / "tla2tools.jar"),
               "control_source_sha256": E.sha(E.HERE / "test_semantic_audit.py"),
               "qualification_scope": "Retained finite evaluator controls; no claim of exhaustive JVM equivalence.",
               "controls": {}}
    for name, plan in control_plans().items():
        profile["controls"][name] = A.execute(plan, E.REPO / "specs/gold", java, 5,
                                              dump_graph=name in {"base", "tautology", "removed"})
    profile["profile_id"] = digest(profile)
    validate_profile(profile)
    return profile


def save(path, data):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def continue_checks(evidence, profile, java, maximum, output):
    import reduce_semantics as R
    R.reduce_evidence(evidence, allow_partial=True)
    validate_profile(profile)
    E.require(runtime(java) == profile["runtime"], "Current runtime differs from qualified profile")
    E.require(evidence["timeout_seconds"] == 5 and evidence["jvm_heap_MiB"] == 512, "Resume limits differ")
    rows = [r for r in E.collect() if r["job"] != "smoke" and r["tlc_pass"]]
    chains = {r["run_id"]: r for r in E.load(E.HERE / "provenance.json")["runs"]}
    keys = {r["run_id"]: (r["spec_id"], E.sha(E.HERE / chains[r["run_id"]]["directory"] / "generation.tla"),
                          r["reference_sha256"], r["configuration_sha256"]) for r in rows}
    original = {r["run_id"]: copy.deepcopy(r) for r in evidence["rows"]}
    results, controls = {}, {}
    for rid, row in original.items():
        results.setdefault(keys[rid], row)
        origin = row.get("reference_self_check_execution", {
            "profile_id": row.get("execution_profile_id", LEGACY_PROFILE), "reused_from_run_id": rid})
        controls.setdefault(keys[rid][2:], (row["reference_self_check"], origin))
    registry = evidence.setdefault("execution_profiles", {})
    registry[profile["profile_id"]] = profile
    E.require(evidence.setdefault("default_execution_profile_id", LEGACY_PROFILE) == LEGACY_PROFILE,
              "Legacy execution profile changed")
    pending = {}
    for rid, key in keys.items():
        if key not in results:
            pending.setdefault(key, rid)
    for key, rid in list(pending.items())[:maximum]:
        row = next(r for r in rows if r["run_id"] == rid)
        directory = E.HERE / chains[rid]["directory"]
        path = E.REPO / row["reference_path"]
        generated, reference, cfg = (directory / "generation.tla").read_text(), path.read_text(), path.with_suffix(".cfg").read_text()
        result = {"run_id": rid, "generated_sha256": key[1], "reference_sha256": key[2],
                  "original_configuration_sha256": key[3], "original_author_tlc_pass": True,
                  "execution_profile_id": profile["profile_id"],
                  "claim_scope": "Bounded reference-derived checks under explicit identity bindings; no natural-language faithfulness certification."}
        for component, plan in zip(R.COMPONENTS[1:], [A.oracle_wrapper(generated, reference, cfg, "properties"),
                A.oracle_wrapper(generated, reference, cfg, "behavior"), A.oracle_wrapper(reference, generated, cfg, "behavior")]):
            result[component] = A.execute(plan, path.parent, java, 5)
        if key[2:] not in controls:
            controls[key[2:]] = (A.reference_control(str(path), java, 5),
                                {"profile_id": profile["profile_id"], "reused_from_run_id": rid})
        control, origin = controls[key[2:]]
        result["reference_self_check"] = copy.deepcopy(control)
        result["reference_self_check_execution"] = copy.deepcopy(origin)
        results[key] = result
        evidence["rows"] = [original[r] if r in original else dict(results[k], run_id=r,
                              execution_reused_from=results[k]["run_id"]) for r, k in keys.items() if k in results]
        evidence.update(completed_unique_outputs=len(results), expected_unique_outputs=len(set(keys.values())),
                        complete=len(results) == len(set(keys.values())))
        R.reduce_evidence(evidence, allow_partial=True)
        save(output, evidence)
        print(json.dumps({"completed_unique_outputs": len(results), "expected_unique_outputs": len(set(keys.values())),
                          "completed_rows": len(evidence["rows"]), "run_id": rid}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--java", required=True)
    parser.add_argument("--profile", required=True, type=Path)
    parser.add_argument("--qualify-runtime", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--max-new-outputs", type=int, default=5)
    args = parser.parse_args()
    E.verify()
    java = str(Path(args.java).resolve())
    E.require(not args.profile.resolve().is_relative_to(E.HERE.resolve()), "Write profiles outside frozen input inventory")
    if args.qualify_runtime:
        save(args.profile, qualify(java))
        return
    E.require(args.output is not None and args.output.exists() and args.max_new_outputs > 0, "Resume checkpoint/batch missing")
    E.require(not args.output.resolve().is_relative_to(E.HERE.resolve()), "Write results outside frozen input inventory")
    continue_checks(E.load(args.output), E.load(args.profile), java, args.max_new_outputs, args.output)


if __name__ == "__main__":
    main()
