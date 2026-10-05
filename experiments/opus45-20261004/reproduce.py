#!/usr/bin/env python3
"""Verify and reduce saved Opus 4.5 evidence, offline with Python's stdlib."""
from __future__ import annotations

import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(REPO / "code/analysis"))
from strict_sany import strict_sany_result
import tla_lib as analysis_helpers


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def files_under(root):
    return {str(p.relative_to(root)) for p in root.rglob("*")
            if p.is_file() and "__pycache__" not in p.parts and p.name != "integrity.json"}


def verify(root=HERE, repo=REPO):
    manifest = load(root / "integrity.json")
    require(files_under(root) == set(manifest["files"]), "File inventory differs from integrity manifest")
    for rel, digest in manifest["files"].items():
        require(sha(root / rel) == digest, f"Artifact hash mismatch: {rel}")
    for rel, digest in manifest["repository_files"].items():
        require(sha(repo / rel) == digest, f"Repository hash mismatch: {rel}")
    for rel, digest in load(root / "protocol.json")["dependencies"].items():
        require(sha(repo / rel) == digest, f"Frozen protocol/input mismatch: {rel}")
    if "input_manifest" in load(root / "protocol.json"):
        frozen_manifest(root)


def frozen_manifest(root=HERE):
    """Read the experiment's original manifest, independently of upstream edits."""
    pin = load(root / "protocol.json")["input_manifest"]
    path = root / pin["path"]
    require(sha(path) == pin["sha256"], "Frozen input manifest hash mismatch")
    records = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]
    manifest = {str(record["spec_id"]): record for record in records}
    require(len(manifest) == len(records), "Duplicate frozen manifest IDs")
    return manifest


def prompt_builder(repo=REPO, root=HERE):
    """Load only the pure templates and cfg-name function from the pinned grader."""
    path = repo / "code/analysis/grading.py"
    require(sha(path) == load(root / "protocol.json")["dependencies"]["code/analysis/grading.py"],
            "Frozen prompt builder hash mismatch")
    tree = ast.parse(path.read_text(encoding="utf-8"))
    selected = [node for node in tree.body if
                (isinstance(node, ast.Assign) and len(node.targets) == 1
                 and isinstance(node.targets[0], ast.Name)
                 and node.targets[0].id in {"GEN_PROMPT", "GEN_PROMPT_CFG"})
                or (isinstance(node, ast.FunctionDef) and node.name == "cfg_names")]
    namespace = {"re": re}
    exec(compile(ast.Module(body=selected, type_ignores=[]), str(path), "exec"), namespace)
    return namespace


def extract_module(text):
    # Exact extraction rule from the frozen author's grading.py.
    match = re.search(r"-{3,}\s*MODULE.*?={4,}", text, re.DOTALL)
    return match.group(0) if match else text


def checked_result(sany, tlc, cfg_text):
    """Require a resolved config, named checks and a nonempty completed TLC pass."""
    semantic = strict_sany_result(sany)
    named = analysis_helpers.checked_names(cfg_text) if cfg_text is not None else {"INVARIANT": [], "PROPERTY": []}
    if tlc is not None:
        require(type(tlc.get("returncode")) is int and isinstance(tlc.get("stdout"), str)
                and isinstance(tlc.get("stderr"), str), "Malformed TLC evidence")
    classified = analysis_helpers.classify(tlc["stdout"], tlc["stderr"]) if tlc else {}
    nonempty = (classified.get("distinct") or 0) > 0
    completed = bool(tlc and re.search(r"Model checking completed|Finished in", tlc["stdout"]))
    gates = [(semantic["passed"], "SANY_semantic_rejection"),
             (cfg_text is not None, "missing_original_configuration"),
             (bool(named["INVARIANT"] or named["PROPERTY"]), "no_enabled_named_property"),
             (nonempty, "nonempty_Init_not_established"),
             (completed, "completed_check_not_established"),
             (bool(tlc and tlc["returncode"] == 0 and classified.get("status") == "pass"
                   and not tlc.get("controlled_timeout")
                   and not re.search(r"(?:^|\n)\s*(?:Error:|.*Exception|.*OutOfMemoryError|.*NoClassDefFoundError)",
                                     tlc["stdout"] + "\n" + tlc["stderr"])), "checker_diagnostics_nonpass")]
    return {"passed": all(ok for ok, _ in gates), "reasons": [reason for ok, reason in gates if not ok],
            "named": named, "nonempty": nonempty, "completed": completed}


def collect(root=HERE, repo=REPO):
    provenance = load(root / "provenance.json")
    protocol = load(root / "protocol.json")
    manifest = frozen_manifest(root)
    builder = prompt_builder(repo, root)
    ids = {str(i) for i in load(repo / "outputs/eval_100_ids.json")}
    rows = []
    seen = set()
    directories = set()
    cohorts = protocol.get("additional_cohorts", [])
    for chain in provenance["runs"]:
        run_id = chain["run_id"]
        require(run_id not in seen, f"Duplicate run: {run_id}")
        seen.add(run_id)
        directory = root / chain["directory"]
        directories.add(directory)
        run = load(directory / "run.json")
        grade = load(directory / "author-grade.json")
        request = load(directory / "request.json")
        response = load(directory / "response.json")
        metadata = load(directory / "metadata.json")
        require(run["run_id"] == run_id == metadata["run_id"], f"Run ID mismatch: {run_id}")
        identity = f'{run["job"]}:{run["spec_id"]}:s{run["sample"]}'
        suffixes = [":" + c["run_id_suffix"] for c in cohorts
                    if c["job"] == run["job"] and run["sample"] in c["samples"]]
        require(run_id == identity or run_id in [identity + suffix for suffix in suffixes], "Malformed run identity")
        mode, desc = {"A1": ("cfgaware", "gpt"), "A2": ("default", "claude"),
                      "A3": ("default", "gpt"), "smoke": ("default", "gpt")}[run["job"]]
        require(run["mode"] == mode and run["description_provider"] == desc, "Condition mismatch")
        require(str(run["spec_id"]) in ids, f"Unknown evaluation ID: {run_id}")
        require(run["model_id"] == grade["model_id"] == request["modelId"] == protocol["model_id"],
                f"Model mismatch: {run_id}")
        require(request["inferenceConfig"] == {"maxTokens": protocol["maxTokens"]}, "Decoding settings differ")
        require(run["max_output_tokens"] == grade["max_tokens"] == protocol["maxTokens"]
                and run["temperature"] is None and grade["temperature"] is None, "Run settings differ")
        require(grade["provider"] == metadata["provider"] == protocol["provider"]
                and metadata["region"] == protocol["region"], "Provider/region mismatch")
        require(str(grade["spec_id"]) == str(run["spec_id"]) and grade["sample"] == run["sample"]
                and grade["mode"] == run["mode"] and grade["desc_provider"] == run["description_provider"],
                "Grade identity mismatch")
        prompt = (directory / "prompt.txt").read_text()
        require(request["messages"] == [{"role": "user", "content": [{"text": prompt}]}], "Prompt/request mismatch")
        require(sha(directory / "prompt.txt") == run["prompt_sha256"], "Prompt hash mismatch")
        require(sha(repo / run["reference_path"]) == run["reference_sha256"], "Reference hash mismatch")
        require(Path(run["reference_path"]).name.startswith(str(run["spec_id"]) + "_"), "Task/reference mismatch")
        cfg = (repo / run["reference_path"]).with_suffix(".cfg")
        require((sha(cfg) if cfg.exists() else None) == run["configuration_sha256"], "Configuration hash mismatch")
        require(run["missing_cfg"] == (not cfg.exists()), "Missing config flag mismatch")
        description = manifest[str(run["spec_id"])]["desc_declarative_" + desc]
        require(isinstance(description, str) and bool(description.strip()), "Empty frozen description")
        template = builder["GEN_PROMPT_CFG" if mode == "cfgaware" else "GEN_PROMPT"]
        reconstructed = template.format(description=description,
            names=builder["cfg_names"](cfg.read_text()) if cfg.exists() else "")
        require(reconstructed.encode("utf-8") == (directory / "prompt.txt").read_bytes(),
                f"Frozen manifest/prompt mismatch: {run_id}")
        require(len(reconstructed.encode("utf-8")) == run["prompt_utf8_bytes"], "Prompt byte count mismatch")
        raw_text = "\n".join(x["text"] for x in response["output"]["message"]["content"] if "text" in x)
        require(bool(raw_text.strip()) and bool((directory / "generation.tla").read_text().strip()), "Empty output")
        require(raw_text == (directory / "raw-response.txt").read_text(), "Raw response extraction mismatch")
        require(extract_module(raw_text) == (directory / "generation.tla").read_text(), "Generated source mismatch")
        require(response["stopReason"] == grade["finish_reason"]
                and response["usage"] == metadata["usage"], "Response metadata mismatch")
        require(grade["tokens_in"] == response["usage"]["inputTokens"]
                and grade["tokens_out"] == response["usage"]["outputTokens"], "Token usage mismatch")
        require(metadata["infrastructure_valid"] is True, "Invalid grading infrastructure")
        for field in ["sany_pass", "tlc_pass"]:
            require(type(grade[field]) is bool, f"Nonboolean archived grade: {run_id}:{field}")
        sany = load(directory / "run_sany-raw.json")
        require(sany["passed"] == grade["sany_pass"], "Archived SANY/raw mismatch")
        strict = strict_sany_result(sany)
        tlc_path = directory / "run_tlc-raw.json"
        tlc = load(tlc_path) if tlc_path.exists() else None
        require((tlc["passed"] if tlc else False) == grade["tlc_pass"], "Archived TLC/raw mismatch")
        timeout = bool(tlc and tlc.get("controlled_timeout"))
        if timeout:
            t = tlc["controlled_timeout"]
            require(tlc["passed"] is False and tlc["returncode"] == -1
                    and t["limit_seconds"] == protocol["TLC_timeout_seconds"]
                    and t["elapsed_seconds"] >= t["limit_seconds"]
                    and t["kill_succeeded"] is True and t["child_reaped"] is True
                    and "TLC2 Version" in t["partial_stdout"], "Unverified timeout")
        require(grade["tlc_pass"] is False or strict["passed"], "TLC pass contradicts strict SANY")
        checked = checked_result(sany, tlc, cfg.read_text() if cfg.exists() else None)
        qualified = grade["tlc_pass"] and checked["passed"]
        qualification_reasons = checked["reasons"] + ([] if grade["tlc_pass"] else ["author_TLC_nonpass"])
        # Untransformed public payloads are also tied to the frozen source hashes.
        for p in directory.iterdir():
            origin = provenance["published_artifacts"].get(str(p.relative_to(root)))
            if origin and origin["transformation"] == "none":
                require(sha(p) == origin["source_sha256"], "Original source digest mismatch")
        rows.append(dict(run, author_sany=grade["sany_pass"], strict_sany=strict["passed"],
                         sany_semantic_ok=strict["passed"], strict_reason=strict["reason"],
                         tlc_pass=grade["tlc_pass"], timeout=timeout, enabled_named_properties=checked["named"],
                         nonempty_init=checked["nonempty"], completed_check=checked["completed"], qualified_tlc_pass=qualified,
                         qualification_reasons=qualification_reasons))
    require(directories == {p.parent for p in (root / "evidence").rglob("run.json")}, "Unindexed evidence")
    require(len(rows) == provenance["logical_outputs"], "Logical output count mismatch")
    for job, samples in [("A1", [0]), ("A2", [0]), ("A3", [1, 2, 3, 4])]:
        samples += [s for c in cohorts if c["job"] == job for s in c["samples"]]
        actual = {(r["spec_id"], r["sample"]) for r in rows if r["job"] == job}
        require(actual == {(sid, sample) for sid in ids for sample in samples}, f"Incomplete {job} matrix")
        require(sum(r["job"] == job for r in rows) == len(ids) * len(samples), f"Duplicated {job} sample slots")
    for sid in ids:
        requests = [r for r in rows if r["job"] == "A3" and r["spec_id"] == sid]
        require(len({r["prompt_sha256"] for r in requests}) == 1, "Matched A3 prompts differ")
        require(len({r["configuration_sha256"] for r in requests}) == 1, "Matched A3 configurations differ")
    return rows


def reduce_rows(rows, repo=REPO, root=HERE):
    protocol = load(root / "protocol.json")
    manifest = frozen_manifest(root)
    result = {"schema": 1, "model_id": protocol["model_id"], "jobs": {}}
    result["input_provenance"] = {"manifest_path": protocol["input_manifest"]["path"],
        "manifest_sha256": protocol["input_manifest"]["sha256"], "manifest_records": len(manifest),
        "prompt_reconstruction_outputs": len(rows),
        "description_fields_used": dict(sorted(Counter("desc_declarative_" + r["description_provider"]
                                                       for r in rows).items()))}
    for job in sorted({r["job"] for r in rows}):
        group = [r for r in rows if r["job"] == job]
        result["jobs"][job] = {
            "outputs": len(group), "specifications": len({r["spec_id"] for r in group}),
            "author_exit_code_sany_passes": sum(r["author_sany"] for r in group),
            "strict_diagnostic_sany_passes": sum(r["strict_sany"] for r in group),
            "author_tlc_passes": sum(r["tlc_pass"] for r in group),
            "author_true_with_semantic_errors": sum(r["author_sany"] and r["strict_reason"] == "semantic_error" for r in group),
            "verified_300s_timeouts": sum(r["timeout"] for r in group),
            "per_sample_tlc_passes": {str(s): sum(r["tlc_pass"] for r in group if r["sample"] == s)
                                      for s in sorted({r["sample"] for r in group})}}
    a3 = [r for r in rows if r["job"] == "A3" and r["sample"] in [1, 2, 3, 4]]
    by_id = {sid: [r for r in a3 if r["spec_id"] == sid] for sid in sorted({r["spec_id"] for r in a3}, key=int)}
    success = {sid for sid, rr in by_id.items() if any(r["tlc_pass"] for r in rr)}
    baseline = load(repo / "outputs/claude-opus-4-5.json")
    old = {str(r["spec_id"]) for r in baseline if r.get("tlc_pass") is True}
    require({str(r["spec_id"]) for r in baseline} == set(by_id), "Released baseline evaluation IDs differ")
    result["matched_a3_pass_at_4"] = {
        "definition": "Observed per-specification any-pass across four matched new samples (n=k=4).",
        "passing_specifications": len(success), "specifications": len(by_id),
        "passing_ids": sorted(success, key=int),
        "pass_count_histogram": {str(k): v for k, v in sorted(Counter(sum(r["tlc_pass"] for r in rr) for rr in by_id.values()).items())}}
    all_a3 = [r for r in rows if r["job"] == "A3"]
    if {r["sample"] for r in all_a3} == {0, 1, 2, 3, 4}:
        five = {sid: [r for r in all_a3 if r["spec_id"] == sid] for sid in by_id}
        for field, label in [("tlc_pass", "matched_a3_pass_at_5"), ("qualified_tlc_pass", "qualified_checked_a3_pass_at_5")]:
            ids5 = {sid for sid, rr in five.items() if any(r[field] for r in rr)}
            result[label] = {"definition": "Observed per-specification any-pass across five matched new samples (n=k=5).",
                "criterion": field, "samples": [0, 1, 2, 3, 4], "passing_specifications": len(ids5),
                "specifications": len(five), "passing_ids": sorted(ids5, key=int),
                "pass_count_histogram": {str(k): v for k, v in sorted(Counter(sum(r[field] for r in rr) for rr in five.values()).items())}}
    result["mixed_baseline_coverage"] = {
        "definition": "Descriptive union of released baseline and four new A3 samples; not certified pass@5.",
        "released_baseline_passes": len(old), "passing_specifications": len(success | old),
        "specifications": len(by_id), "baseline_only_ids": sorted(old - success, key=int),
        "baseline_sha256": sha(repo / "outputs/claude-opus-4-5.json"),
        "strict_pass_at_5_certified": False,
        "missing_baseline_provenance": ["request model ID", "provider", "max output tokens", "decoding settings"]}
    result["strict_parser_corrections"] = [{"run_id": r["run_id"], "reason": r["strict_reason"]}
                                           for r in rows if r["author_sany"] != r["strict_sany"]]
    result["timeout_ids"] = [r["run_id"] for r in rows if r["timeout"]]
    result["row_reconciliation"] = [{"run_id": r["run_id"], "author_sany_pass": r["author_sany"],
        "sany_semantic_ok": r["sany_semantic_ok"], "compiler_reason": r["strict_reason"],
        "author_tlc_pass": r["tlc_pass"], "qualified_checked_tlc_pass": r["qualified_tlc_pass"],
        "qualification_reasons": r["qualification_reasons"], "configuration_source": "original_reference" if not r["missing_cfg"] else "absent",
        "nonempty_Init_established": r["nonempty_init"], "completed_check": r["completed_check"],
        "enabled_named_properties": r["enabled_named_properties"]} for r in rows]
    evaluation_ids = {str(i) for i in load(repo / "outputs/eval_100_ids.json")}
    without_cfg = {r["spec_id"] for r in rows if r["missing_cfg"]}
    single_state = {str(r["spec_id"]) for r in load(repo / "outputs/audit/fixture_audit.json") if r.get("distinct") == 1}
    result["evaluation_strata"] = {}
    for name, selected in [("full_primary", evaluation_ids), ("with_original_configuration", evaluation_ids - without_cfg),
                           ("without_missing_cfg_or_single_state_fixtures", evaluation_ids - without_cfg - single_state)]:
        result["evaluation_strata"][name] = {"specifications": len(selected), "excluded_ids": sorted(evaluation_ids - selected, key=int),
            "jobs": {j: {"outputs": len(rr), "author_tlc_passes": sum(r["tlc_pass"] for r in rr),
                          "qualified_checked_tlc_passes": sum(r["qualified_tlc_pass"] for r in rr),
                          "sany_semantic_ok_count": sum(r["sany_semantic_ok"] for r in rr)}
                     for j in ["A1", "A2", "A3"] for rr in [[r for r in rows if r["job"] == j and r["spec_id"] in selected]]}}
    a2 = {r["spec_id"]: r for r in rows if r["job"] == "A2"}
    common = set(a2) & set(by_id)
    result["paired_default_description_comparison"] = {"definition": "Descriptive paired task comparison: one A2 Claude-description sample vs mean of four matched default/GPT-description A3 samples. No causal provider-effect claim; description equivalence requires independent review.",
        "common_task_count": len(common), "rows": [{"spec_id": sid, "source_repo": manifest[sid]["source_repo"],
        "a2_author_tlc_pass": a2[sid]["tlc_pass"], "a3_author_tlc_pass_fraction": sum(r["tlc_pass"] for r in by_id[sid]) / len(by_id[sid]),
        "paired_difference": float(a2[sid]["tlc_pass"]) - sum(r["tlc_pass"] for r in by_id[sid]) / len(by_id[sid])}
        for sid in sorted(common, key=int)]}
    comparison = result["paired_default_description_comparison"]
    comparison["repository_sensitivity"] = {source: {"tasks": len(rr), "mean_paired_difference": sum(r["paired_difference"] for r in rr) / len(rr)}
        for source in sorted({r["source_repo"] for r in comparison["rows"]})
        for rr in [[r for r in comparison["rows"] if r["source_repo"] == source]]}
    comparison["mean_paired_difference"] = sum(r["paired_difference"] for r in comparison["rows"]) / len(common)
    return result


def render_tables(report):
    lines = ["| Experiment | Description source | Mode | Outputs | Archived SANY flag | sany_semantic_ok | Archived TLC | Qualified checked TLC |",
             "|---|---|---|---:|---:|---:|---:|---:|"]
    info = {"A1": ("GPT declarative", "Configuration-aware"), "A2": ("Claude declarative", "Default"),
            "A3": ("GPT declarative", "Default, matched samples " + ",".join(report["jobs"]["A3"]["per_sample_tlc_passes"])),
            "smoke": ("GPT declarative", "Separate smoke")}
    for job in ["A1", "A2", "A3", "smoke"]:
        r = report["jobs"][job]
        qualified = report["evaluation_strata"]["full_primary"]["jobs"].get(job, {}).get("qualified_checked_tlc_passes", 0)
        lines.append(f'| {job} | {info[job][0]} | {info[job][1]} | {r["outputs"]} | {r["author_exit_code_sany_passes"]} | {r["strict_diagnostic_sany_passes"]} | {r["author_tlc_passes"]} | {qualified} |')
    lines += ["", "| Sensitivity stratum | Tasks | A1 archived TLC / outputs | A2 archived TLC / outputs | A3 archived TLC / outputs |",
              "|---|---:|---:|---:|---:|"]
    for name, s in report["evaluation_strata"].items():
        values = [str(s["specifications"])]
        values += [f'{s["jobs"][j]["author_tlc_passes"]}/{s["jobs"][j]["outputs"]}' for j in ["A1", "A2", "A3"]]
        lines.append("| " + name + " | " + " | ".join(values) + " |")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="also compare the saved derived report")
    parser.add_argument("--json", action="store_true", help="print machine-readable reductions")
    args = parser.parse_args()
    verify()
    report = reduce_rows(collect())
    if args.check:
        require(report == load(HERE / "report.json"), "Saved report does not derive from evidence")
        require(render_tables(report) == (HERE / "tables.md").read_text(), "Markdown tables do not derive from evidence")
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print("Opus 4.5 / Bedrock / maxTokens=16000 / provider-default temperature")
        print("Job     outputs   archived SANY   strict SANY   archived TLC   300s timeouts")
        for job, r in report["jobs"].items():
            print(f'{job:7s} {r["outputs"]:7d} {r["author_exit_code_sany_passes"]:15d}'
                  f' {r["strict_diagnostic_sany_passes"]:13d} {r["author_tlc_passes"]:14d}'
                  f' {r["verified_300s_timeouts"]:15d}')
        a = report["matched_a3_pass_at_4"]
        print(f'Matched new A3 pass@4: {a["passing_specifications"]}/{a["specifications"]}')
        if "matched_a3_pass_at_5" in report:
            a = report["matched_a3_pass_at_5"]
            q = report["qualified_checked_a3_pass_at_5"]
            print(f'Matched new A3 archived-protocol pass@5: {a["passing_specifications"]}/{a["specifications"]}')
            print(f'Named-check/nonempty/completion-qualified pass@5: {q["passing_specifications"]}/{q["specifications"]}')
        m = report["mixed_baseline_coverage"]
        print(f'Mixed released baseline + A3 coverage: {m["passing_specifications"]}/{m["specifications"]}; uncertified pass@5')


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as exc:
        raise SystemExit(f"Evidence verification failed: {exc}")
