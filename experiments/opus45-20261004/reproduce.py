#!/usr/bin/env python3
"""Verify and reduce saved Opus 4.5 evidence, offline with Python's stdlib."""
from __future__ import annotations

import argparse
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


def extract_module(text):
    # Exact extraction rule from the frozen author's grading.py.
    match = re.search(r"-{3,}\s*MODULE.*?={4,}", text, re.DOTALL)
    return match.group(0) if match else text


def collect(root=HERE, repo=REPO):
    provenance = load(root / "provenance.json")
    protocol = load(root / "protocol.json")
    ids = {str(i) for i in load(repo / "outputs/eval_100_ids.json")}
    rows = []
    seen = set()
    directories = set()
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
        require(run_id == f'{run["job"]}:{run["spec_id"]}:s{run["sample"]}', "Malformed run identity")
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
        cfg = (repo / run["reference_path"]).with_suffix(".cfg")
        require((sha(cfg) if cfg.exists() else None) == run["configuration_sha256"], "Configuration hash mismatch")
        require(run["missing_cfg"] == (not cfg.exists()), "Missing config flag mismatch")
        raw_text = "\n".join(x["text"] for x in response["output"]["message"]["content"] if "text" in x)
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
        # Untransformed public payloads are also tied to the frozen source hashes.
        for p in directory.iterdir():
            origin = provenance["published_artifacts"].get(str(p.relative_to(root)))
            if origin and origin["transformation"] == "none":
                require(sha(p) == origin["source_sha256"], "Original source digest mismatch")
        rows.append(dict(run, author_sany=grade["sany_pass"], strict_sany=strict["passed"],
                         strict_reason=strict["reason"], tlc_pass=grade["tlc_pass"], timeout=timeout))
    require(directories == {p.parent for p in (root / "evidence").rglob("run.json")}, "Unindexed evidence")
    require(len(rows) == provenance["logical_outputs"], "Logical output count mismatch")
    for job, samples in [("A1", [0]), ("A2", [0]), ("A3", [1, 2, 3, 4])]:
        actual = {(r["spec_id"], r["sample"]) for r in rows if r["job"] == job}
        require(actual == {(sid, sample) for sid in ids for sample in samples}, f"Incomplete {job} matrix")
    return rows


def reduce_rows(rows, repo=REPO):
    result = {"schema": 1, "model_id": load(HERE / "protocol.json")["model_id"], "jobs": {}}
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
    a3 = [r for r in rows if r["job"] == "A3"]
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
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="also compare the saved derived report")
    parser.add_argument("--json", action="store_true", help="print machine-readable reductions")
    args = parser.parse_args()
    verify()
    report = reduce_rows(collect())
    if args.check:
        require(report == load(HERE / "report.json"), "Saved report does not derive from evidence")
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
        m = report["mixed_baseline_coverage"]
        print(f'Mixed released baseline + A3 coverage: {m["passing_specifications"]}/{m["specifications"]}; uncertified pass@5')


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as exc:
        raise SystemExit(f"Evidence verification failed: {exc}")
