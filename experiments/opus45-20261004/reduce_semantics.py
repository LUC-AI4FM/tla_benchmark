#!/usr/bin/env python3
"""Verify every independent check against its source/config and reduce raw logs."""
from collections import Counter
import argparse
import json
from pathlib import Path
import re

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
    import continue_reference_audit as C
    profiles = evidence.get("execution_profiles", {})
    E.require(evidence.get("default_execution_profile_id", C.LEGACY_PROFILE) == C.LEGACY_PROFILE,
              "Original execution profile changed")
    for pid, profile in profiles.items():
        C.validate_profile(profile)
        E.require(pid == profile["profile_id"], "Execution profile registry differs")
        builds = re.findall(r"\(build ([^\s),]+)", profile["runtime"]["java_version_output"])
        E.require(bool(builds) and all(b == profile["runtime"]["java_build"] for b in builds),
                  "Recorded Java version output contradicts profile build")

    def verify_runtime_banner(record, profile_id):
        raw = record.get("raw", {})
        text = raw.get("tlc", {}).get("stdout", "") or raw.get("timeout", {}).get("partial_stdout", "")
        banner = next((line for line in text.splitlines() if line.startswith("Running ") and "Model-Checking" in line), "")
        if not banner:
            E.require(record["status"] != "holds" and not record.get("semantic_kill"),
                      "Completed checker result lacks runtime banner")
            return
        if profile_id == C.LEGACY_PROFILE:
            version, system = "11.0.25", "Mac OS X"
        else:
            runtime = profiles[profile_id]["runtime"]
            version = runtime["java_build"].split("+")[0]
            system = {"Darwin": "Mac OS X", "Linux": "Linux"}.get(runtime["system"], runtime["system"])
        E.require(re.search(r"Eclipse Adoptium " + re.escape(version) + r" 64bit", banner)
                  and system in banner, "Raw checker runtime contradicts execution profile")

    for pid, profile in profiles.items():
        for record in profile["controls"].values():
            verify_runtime_banner(record, pid)
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
        profile_id = row.get("execution_profile_id", C.LEGACY_PROFILE)
        E.require(profile_id == C.LEGACY_PROFILE or profile_id in profiles, "Missing execution profile receipt")
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
            component_profile = row.get("reference_self_check_execution", {}).get("profile_id", profile_id) if component == "reference_self_check" else profile_id
            E.require(component_profile == C.LEGACY_PROFILE or component_profile in profiles,
                      "Missing component execution profile receipt")
            verify_runtime_banner(row[component], component_profile)
        E.require(row["execution_reused_from"] in observed, "Unindexed reused execution")
        reused = observed[row["execution_reused_from"]]
        E.require(reused["generated_sha256"] == row["generated_sha256"]
                  and input_keys[reused["run_id"]] == input_keys[rid]
                  and all(row[c] == reused[c] for c in COMPONENTS), "Reused execution differs")
        E.require(profile_id == reused.get("execution_profile_id", C.LEGACY_PROFILE), "Reused execution profile differs")
        control_origin = row.get("reference_self_check_execution")
        if control_origin:
            control_source = observed.get(control_origin["reused_from_run_id"])
            E.require(control_source is not None
                      and row["reference_sha256"] == control_source["reference_sha256"]
                      and row["original_configuration_sha256"] == control_source["original_configuration_sha256"]
                      and row["reference_self_check"] == control_source["reference_self_check"],
                      "Reused reference control differs")
            source_origin = control_source.get("reference_self_check_execution", {
                "profile_id": control_source.get("execution_profile_id", C.LEGACY_PROFILE)})
            E.require(control_origin["profile_id"] == source_origin["profile_id"], "Reference control profile differs")
        statuses = {c: row[c]["status"] for c in COMPONENTS}
        control_holds = statuses["reference_self_check"] == "holds"
        behavior_holds = control_holds and all(statuses[c] == "holds" for c in COMPONENTS[2:])
        qualified = original["qualified_tlc_pass"] and all(v == "holds" for v in statuses.values())
        counterexample = control_holds and any(row[c].get("semantic_kill") is True for c in COMPONENTS[1:])
        reconciled.append({"run_id": rid, "spec_id": original["spec_id"], "job": original["job"], "sample": original["sample"],
            "mode": original["mode"], "description_provider": original["description_provider"],
            "execution_profile_id": profile_id,
            "reference_self_check_execution": control_origin,
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
    a3_profiles = sorted({r["execution_profile_id"] for r in reconciled if r["job"] == "A3"})
    any_pass = {"samples": sorted({r["sample"] for r in a3}), "certified_complete_audit": evidence["complete"],
                "observed_execution_profile_ids": a3_profiles, "single_execution_profile": len(a3_profiles) == 1,
                "assessment_scope": "Bounded reference checks with the explicitly recorded execution profiles; no natural-language faithfulness certification."}
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
    missing_cfg = {r["spec_id"] for r in a3 if r["missing_cfg"]}
    single_state = {str(r["spec_id"]) for r in E.load(E.REPO / "outputs/audit/fixture_audit.json") if r.get("distinct") == 1}
    strata = {}
    for name, selected in [("full_primary", a3_ids), ("with_original_configuration", a3_ids - missing_cfg),
            ("without_missing_cfg_or_single_state_fixtures", a3_ids - missing_cfg - single_state)]:
        strata[name] = {"specifications": len(selected), "excluded_ids": sorted(a3_ids - selected, key=int),
                        "certified_complete_audit": evidence["complete"]}
        if evidence["complete"]:
            strata[name].update(passing_specifications=len(passing & selected), passing_ids=sorted(passing & selected, key=int))
    return {"schema": 1, "assessment_phase": "post_generation_validation_of_frozen_reference_contracts", "complete": evidence["complete"],
        "claim_scope": "Bounded reference-derived named properties and both behavior inclusions under explicit identity bindings; not natural-language faithfulness certification.",
        "audit_script_sha256": evidence["audit_script_sha256"], "runtime": evidence["runtime"], "timeout_seconds": evidence["timeout_seconds"], "jvm_heap_MiB": evidence["jvm_heap_MiB"],
        "passing_outputs_audited": len(reconciled), "passing_outputs_expected": len(expected),
        "unexecuted_run_ids": sorted(set(expected) - set(observed)),
        "unique_generated_outputs_executed": len(unique), "unique_generated_outputs_expected": len(full_unique), "jobs": by_job,
        "target_scope": target_scope,
        "execution_profiles": profiles,
        "execution_profile_output_counts": dict(sorted(Counter(r["execution_profile_id"] for r in reconciled).items())),
        "external_reference_qualified_a3_any_pass": any_pass,
        "external_reference_a3_evaluation_strata": strata,
        "row_reconciliation": reconciled}


def render_tables(report):
    lines = ["# Independent bounded reference audit", "",
             f"Coverage: {report['passing_outputs_audited']}/{report['passing_outputs_expected']} passing output rows; "
             f"{report['unique_generated_outputs_executed']}/{report['unique_generated_outputs_expected']} unique input keys.", "",
             "| Condition | Passing rows audited | External reference-qualified outputs | Counterexample outputs | Outputs with unresolved components |",
             "|---|---:|---:|---:|---:|"]
    for job, row in report["jobs"].items():
        lines.append(f"| {job} | {row['archived_passing_outputs_audited']}/{row['archived_passing_outputs_expected']} | "
                     f"{row['observed_external_reference_qualified_passes']} | {row['reference_counterexamples']} | {row['unresolved_outputs']} |")
    lines += ["", "Counterexample and unresolved columns can overlap when different components have different outcomes.",
              "External qualification requires the original named-check/nonempty qualification and all four reference components to hold.", "",
              "| A3 task stratum | External reference-qualified any-pass across samples 0–4 |", "|---|---:|"]
    for name, row in report["external_reference_a3_evaluation_strata"].items():
        value = f"{row['passing_specifications']}/{row['specifications']}" if report["complete"] else "Incomplete audit; no population score certified"
        lines.append(f"| {name} | {value} |")
    lines += ["", "| Execution profile | Output rows |", "|---|---:|"]
    for pid, count in report["execution_profile_output_counts"].items():
        label = "Original Mac / Temurin 11.0.25+9" if pid == "original-mac-temurin11" else (
            report["execution_profiles"][pid]["runtime"]["system"] + " / Temurin " + report["execution_profiles"][pid]["runtime"]["java_build"])
        lines.append(f"| {label} | {count} |")
    lines += ["", "Reference controls retain their separately recorded execution source/profile when reused.",
              "These are bounded results under mixed execution profiles, not natural-language faithfulness certification.",
              "All 100 description-equivalence cases remain unreviewed.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=E.HERE / "semantic-evidence.json")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--allow-partial", action="store_true", help="verify an explicitly incomplete checkpoint without certifying a population score")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--tables", action="store_true", help="render the independently derived audit tables")
    args = parser.parse_args()
    E.verify()
    report = reduce_evidence(E.load(args.evidence), allow_partial=args.allow_partial)
    if args.check:
        E.require(report == E.load(E.HERE / "semantic-report.json"), "Semantic report does not derive from checker evidence")
        E.require(render_tables(report) == (E.HERE / "semantic-tables.md").read_text(), "Semantic tables do not derive from checker evidence")
        if report["complete"]:
            receipt = E.load(E.HERE / "execution-receipt.json")
            profile = report["execution_profiles"][receipt["profile_id"]]
            E.require(receipt["runtime"] == profile["runtime"] and receipt["limits"] == profile["limits"], "Launch/runtime receipt differs")
            E.require(receipt["final_unique_checks"] == report["unique_generated_outputs_executed"]
                      == receipt["prior_completed_unique_checks"] + receipt["new_unique_checks_completed"]
                      and receipt["final_passing_records"] == report["passing_outputs_audited"]
                      == receipt["prior_completed_records"] + receipt["new_output_records_reconciled"]
                      and receipt["new_output_records_reconciled"] == report["execution_profile_output_counts"][receipt["profile_id"]],
                      "Completion receipt inventory differs")
            projection = E.load(args.evidence)["public_log_projection"]
            E.require(receipt["final_raw_checkpoint_sha256"] == projection["source_checkpoint_sha256"]
                      and receipt["prior_checkpoint_sha256"] == projection["preserved_checkpoint_sha256"], "Checkpoint receipt lineage differs")
    print(render_tables(report) if args.tables else (json.dumps(report, indent=2) if args.json else json.dumps(report["jobs"], indent=2)))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as exc:
        raise SystemExit(f"Independent evidence verification failed: {exc}")
