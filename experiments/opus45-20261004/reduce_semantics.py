#!/usr/bin/env python3
"""Verify every independent check against its source/config and reduce raw logs."""
from collections import Counter
import argparse
import json
from pathlib import Path

import semantic_audit as A
E = A.E
COMPONENTS = ["reference_self_check", "reference_properties",
              "reference_allows_generated_behaviors", "generated_allows_reference_behaviors"]


def verify_execution(record, plan, reference_dir):
    if plan["status"] != "ready":
        E.require(record == plan, "Unresolved plan differs from recorded outcome")
        return
    dependencies = A.resolve_dependencies(plan["modules"], reference_dir)
    if dependencies["status"] != "ready":
        E.require(record == dependencies, "Unresolved dependencies differ")
        return
    E.require(record["cfg"] == plan["cfg"] and record["config_kind"] == plan["config_kind"],
              "Independent check configuration differs")
    E.require(record["mapping"] == plan.get("mapping", {}) and record["roots"] == plan.get("roots", []),
              "Independent oracle/mapping differs")
    expected_hashes = {name: A.hashlib.sha256(text.encode()).hexdigest()
                       for name, text in dependencies["modules"].items()}
    E.require(record["module_sha256"] == expected_hashes, "Independent staged modules differ")
    raw = record["raw"]
    reclassified = A.verdict(raw["sany"], raw.get("tlc"), timeout="timeout" in raw)
    E.require(all(record.get(k) == v for k, v in reclassified.items()),
              "Recorded outcome does not derive from raw checker logs")


def reduce_evidence(evidence, allow_partial=False):
    E.require(type(evidence["complete"]) is bool, "Malformed audit completeness flag")
    E.require(evidence["complete"] or allow_partial, "Independent audit is incomplete")
    E.require(evidence["audit_script_sha256"] == E.sha(E.HERE / "semantic_audit.py"), "Audit evaluator version differs")
    E.require("11.0.25+9" in evidence["runtime"] and 1 <= evidence["timeout_seconds"] <= 300,
              "Independent audit runtime/settings differ")
    E.require(evidence["jvm_heap_MiB"] == 512, "Independent audit heap differs")
    original_rows = E.collect()
    expected = {r["run_id"]: r for r in original_rows if r["job"] != "smoke" and r["tlc_pass"]}
    observed = {r["run_id"]: r for r in evidence["rows"]}
    E.require(len(observed) == len(evidence["rows"]) and bool(observed) and set(observed) <= set(expected)
              and (not evidence["complete"] or set(observed) == set(expected)),
              "Independent audit passing-output coverage differs")
    chains = {r["run_id"]: r for r in E.load(E.HERE / "provenance.json")["runs"]}
    # Reuse checker executions only for identical task/module/reference/config inputs.
    # Every experimental condition and sample retains its own reconciled output row.
    input_keys = {rid: (r["spec_id"], E.sha(E.HERE / chains[rid]["directory"] / "generation.tla"),
                       r["reference_sha256"], r["configuration_sha256"])
                  for rid, r in expected.items()}
    compact_keys = {}
    for key in input_keys.values():
        compact_keys.setdefault(key[:2], set()).add(key)
    E.require(all(len(keys) == 1 for keys in compact_keys.values()),
              "Compact evaluator key aliases different reference/configuration inputs")
    unique = {input_keys[rid] for rid in observed}
    full_unique = set(input_keys.values())
    E.require(set(observed) == {rid for rid, key in input_keys.items() if key in unique},
              "Independent audit condition/sample alias coverage differs")
    E.require(evidence["completed_unique_outputs"] == len(unique) and evidence["expected_unique_outputs"] == len(full_unique),
              "Independent execution inventory differs")
    reconciled = []
    for rid, row in observed.items():
        original = expected[rid]
        directory = E.HERE / chains[rid]["directory"]
        path = E.REPO / original["reference_path"]
        generated, reference, cfg = (directory / "generation.tla").read_text(), path.read_text(), path.with_suffix(".cfg").read_text()
        E.require(row["generated_sha256"] == E.sha(directory / "generation.tla")
                  and row["reference_sha256"] == E.sha(path)
                  and row["original_configuration_sha256"] == E.sha(path.with_suffix(".cfg")), "Independent input digests differ")
        control = {"status": "ready", "modules": {A.G.module_name(reference): reference},
                   "primary": A.G.module_name(reference), "cfg": cfg, "config_kind": "original_reference"}
        plans = [control, A.oracle_wrapper(generated, reference, cfg, "properties"),
                 A.oracle_wrapper(generated, reference, cfg, "behavior"),
                 A.oracle_wrapper(reference, generated, cfg, "behavior")]
        for component, plan in zip(COMPONENTS, plans):
            verify_execution(row[component], plan, path.parent)
        E.require(row["execution_reused_from"] in observed, "Unindexed reused execution")
        reused = observed[row["execution_reused_from"]]
        E.require(reused["generated_sha256"] == row["generated_sha256"]
                  and input_keys[reused["run_id"]] == input_keys[rid]
                  and all(row[c] == reused[c] for c in COMPONENTS), "Reused execution differs")
        statuses = {c: row[c]["status"] for c in COMPONENTS}
        control_holds = statuses["reference_self_check"] == "holds"
        behavior_holds = control_holds and all(statuses[c] == "holds" for c in COMPONENTS[2:])
        qualified = original["qualified_tlc_pass"] and all(v == "holds" for v in statuses.values())
        counterexample = control_holds and any(row[c].get("semantic_kill") is True for c in COMPONENTS[1:])
        reconciled.append({"run_id": rid, "spec_id": original["spec_id"], "job": original["job"], "sample": original["sample"],
            "mode": original["mode"], "description_provider": original["description_provider"],
            "execution_input_key": dict(zip(["spec_id", "generated_sha256", "reference_sha256", "configuration_sha256"], input_keys[rid])),
            "author_tlc_pass": True, "qualified_checked_tlc_pass": original["qualified_tlc_pass"],
            "external_reference_qualified_tlc_pass": qualified,
            "behavior_comparison_holds_under_identity_bindings": behavior_holds,
            "independent_reference_counterexample_observed": counterexample,
            "outcomes": statuses, "identity_mappings": {c: row[c].get("mapping") for c in COMPONENTS[1:]},
            "unresolved_components": [c for c in COMPONENTS if statuses[c] != "holds"
                                      and not row[c].get("semantic_kill")],
            "execution_reused_from": row["execution_reused_from"]})
    qualified_ids = {r["run_id"] for r in reconciled if r["external_reference_qualified_tlc_pass"]}
    by_job = {}
    for job in ["A1", "A2", "A3"]:
        rr = [r for r in reconciled if r["job"] == job]
        all_rows = [r for r in original_rows if r["job"] == job]
        by_job[job] = {"experimental_outputs": len(all_rows), "experimental_specifications": len({r["spec_id"] for r in all_rows}),
            "archived_passing_outputs_expected": sum(r["tlc_pass"] for r in all_rows),
            "archived_passing_outputs_audited": len(rr), "observed_external_reference_qualified_passes": sum(r["run_id"] in qualified_ids for r in all_rows),
            "reference_counterexamples": sum(r["independent_reference_counterexample_observed"] for r in rr),
            "unresolved_outputs": sum(bool(r["unresolved_components"]) for r in rr),
            "component_outcomes": {c: dict(sorted(Counter(r["outcomes"][c] for r in rr).items())) for c in COMPONENTS}}
    a3 = [r for r in original_rows if r["job"] == "A3"]
    a3_ids = {r["spec_id"] for r in a3}
    passing = {r["spec_id"] for r in a3 if r["run_id"] in qualified_ids}
    any_pass = {"samples": sorted({r["sample"] for r in a3}), "certified_complete_audit": evidence["complete"]}
    if evidence["complete"]:
        any_pass.update(passing_specifications=len(passing), specifications=len(a3_ids), passing_ids=sorted(passing, key=int))
    else:
        any_pass.update(reason="Incomplete audit: unexecuted outputs remain unresolved; no population score certified.",
                        observed_passing_ids=sorted(passing, key=int))
    fresh_ids = {rid for rid, r in expected.items() if r["job"] == "A3" and r["sample"] == 0}
    original_keys = {key for rid, key in input_keys.items() if rid not in fresh_ids}
    fresh_keys = {input_keys[rid] for rid in fresh_ids}
    target_scope = {
        "experimental_outputs": sum(r["job"] != "smoke" for r in original_rows),
        "separate_smoke_outputs": sum(r["job"] == "smoke" for r in original_rows),
        "a3_samples": sorted({r["sample"] for r in a3}),
        "original_passing_output_rows": len(expected) - len(fresh_ids),
        "original_unique_input_keys": len(original_keys),
        "fresh_sample0_passing_output_rows": len(fresh_ids),
        "fresh_sample0_new_unique_input_keys": len(fresh_keys - original_keys),
        "fresh_sample0_reused_input_keys": len(fresh_keys & original_keys),
        "passing_output_rows_by_condition": dict(sorted(Counter(r["job"] for r in expected.values()).items())),
        "execution_key_fields": ["spec_id", "generated_sha256", "reference_sha256", "configuration_sha256"],
    }
    return {"schema": 1, "assessment_phase": "post_generation_validation_of_frozen_reference_contracts", "complete": evidence["complete"],
        "claim_scope": "Bounded reference-derived named properties and both behavior inclusions under explicit identity bindings; not natural-language faithfulness certification.",
        "audit_script_sha256": evidence["audit_script_sha256"], "runtime": evidence["runtime"], "timeout_seconds": evidence["timeout_seconds"], "jvm_heap_MiB": evidence["jvm_heap_MiB"],
        "passing_outputs_audited": len(reconciled), "passing_outputs_expected": len(expected),
        "unexecuted_run_ids": sorted(set(expected) - set(observed)),
        "unique_generated_outputs_executed": len(unique), "unique_generated_outputs_expected": len(full_unique), "jobs": by_job,
        "target_scope": target_scope,
        "external_reference_qualified_a3_any_pass": any_pass,
        "row_reconciliation": reconciled}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=E.HERE / "semantic-evidence.json")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--allow-partial", action="store_true", help="verify an explicitly incomplete checkpoint without certifying a population score")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    E.verify()
    report = reduce_evidence(E.load(args.evidence), allow_partial=args.allow_partial)
    if args.check:
        E.require(report == E.load(E.HERE / "semantic-report.json"), "Semantic report does not derive from checker evidence")
    print(json.dumps(report, indent=2) if args.json else json.dumps(report["jobs"], indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as exc:
        raise SystemExit(f"Independent evidence verification failed: {exc}")
