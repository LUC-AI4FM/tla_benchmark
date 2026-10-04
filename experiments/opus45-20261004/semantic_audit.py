#!/usr/bin/env python3
"""Independent reference-derived checks for saved passing outputs, without APIs.

The frozen reference supplies the oracle through an explicit TLA+ INSTANCE.
This post-generation audit does not invent natural-language requirements.
Unresolved identity mappings, parse failures and timeouts remain unresolved.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import reproduce as E
sys.path[:0] = [str(E.REPO / "code/analysis"), str(E.REPO / "code")]
import grading as G
import tla_lib as L


def declarations(text, kind):
    """Conservative declaration inventory; SANY subsequently validates bindings."""
    code = L.strip_tla_comments(text).split("====", 1)[0]
    names = []
    keyword = "VARIABLES?" if kind == "variables" else "CONSTANTS?"
    lines = code.splitlines()
    for i, line in enumerate(lines):
        m = re.match(r"^\s*" + keyword + r"\s+(.+)", line)
        if not m:
            continue
        chunks = [m.group(1)]
        for next_line in lines[i + 1:]:
            if not next_line.strip():
                continue
            if re.search(r"==", next_line) or re.match(r"^\s*(VARIABLE|CONSTANT|EXTENDS|ASSUME|THEOREM|RECURSIVE|MODULE|LOCAL)\b", next_line):
                break
            if not re.fullmatch(r"[\s\w,()_]+", next_line):
                break
            chunks.append(next_line.strip())
        # Operator-valued constants such as C(_) retain their declared name.
        for declaration in re.split(r",\s*(?![^()]*\))", " ".join(chunks)):
            match = re.match(r"\s*([A-Za-z_]\w*)", declaration)
            if match:
                names.append(match.group(1))
    return list(dict.fromkeys(names))


def replace_header(text, name):
    return re.sub(r"(-{3,}\s*MODULE\s+)\w+", lambda m: m.group(1) + name, text, count=1)


def cfg_without_checks(cfg):
    lines = []
    skipping = False
    for line in L.strip_cfg_comments(cfg).splitlines():
        tokens = line.split()
        if tokens and tokens[0] in L.CFG_KEYWORDS:
            skipping = tokens[0] in {"INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES"}
        if not skipping:
            lines.append(line)
    return "\n".join(lines) + "\n"


def oracle_wrapper(target, reference, cfg, kind):
    """Return exact oracle source, explicit identity mapping, and derived cfg."""
    generated_name = G.module_name(target)
    oracle_name = "AuditOracle" + hashlib.sha256(reference.encode()).hexdigest()[:10]
    wrapper_name = "AuditSubject"
    source_vars = set(declarations(reference, "variables"))
    target_vars = set(declarations(target, "variables"))
    source_constants = set(declarations(reference, "constants"))
    target_constants = set(declarations(target, "constants"))
    if not source_vars <= target_vars or not source_constants <= target_constants:
        return {"status": "unresolved_mapping", "source_variables": sorted(source_vars),
                "target_variables": sorted(target_vars), "source_constants": sorted(source_constants),
                "target_constants": sorted(target_constants)}
    if kind == "behavior" and source_vars != target_vars:
        return {"status": "unresolved_mapping", "reason": "Behavior comparison requires identical variable interfaces"}
    sections = L.parse_cfg(cfg)
    checks = L.checked_names(cfg)
    roots = checks["INVARIANT"] + checks["PROPERTY"]
    if kind == "properties" and not roots:
        return {"status": "no_named_property"}
    if kind == "behavior":
        roots = sections.get("SPECIFICATION", [])
        if len(roots) != 1:
            return {"status": "unresolved_behavior_contract", "reason": "Original cfg does not select one SPECIFICATION"}
    mapping = {name: name for name in sorted(source_vars | source_constants)}
    instance = "Oracle == INSTANCE " + oracle_name
    if mapping:
        instance += " WITH " + ", ".join(f"{s} <- {t}" for s, t in mapping.items())
    aliases = {name: f"ExternalCheck{i}" for i, name in enumerate(roots)}
    wrapper = f"---- MODULE {wrapper_name} ----\nEXTENDS {generated_name}\n{instance}\n"
    wrapper += "\n".join(f"{alias} == Oracle!{name}" for name, alias in aliases.items()) + "\n====\n"
    derived_cfg = cfg_without_checks(cfg)
    if kind == "properties":
        for keyword in ["INVARIANT", "PROPERTY"]:
            if checks[keyword]:
                derived_cfg += keyword + " " + " ".join(aliases[n] for n in checks[keyword]) + "\n"
    else:
        derived_cfg += "PROPERTY " + aliases[roots[0]] + "\n"
    return {"status": "ready", "modules": {generated_name: target, oracle_name: replace_header(reference, oracle_name),
                                               wrapper_name: wrapper}, "primary": wrapper_name,
            "cfg": derived_cfg, "config_kind": "derived_audit_from_original_reference",
            "mapping": mapping, "roots": roots, "check_aliases": aliases}


def verdict(sany, tlc, timeout=False):
    """Fail closed: compiler/runtime failures are never semantic mutation kills."""
    semantic = E.strict_sany_result(sany)
    if not semantic["passed"]:
        return {"status": "sany_rejected", "sany_semantic_ok": False, "reason": semantic["reason"], "semantic_kill": False}
    if timeout:
        return {"status": "timeout", "sany_semantic_ok": True, "semantic_kill": False}
    if tlc is None:
        return {"status": "missing_checker_evidence", "semantic_kill": False}
    E.require(type(tlc.get("returncode")) is int and isinstance(tlc.get("stdout"), str)
              and isinstance(tlc.get("stderr"), str), "Malformed TLC evidence")
    classified = L.classify(tlc["stdout"], tlc["stderr"])
    text = tlc["stdout"] + "\n" + tlc["stderr"]
    if re.search(r"Error: The invariant of \S+ is equal to FALSE", text):
        return {"status": "false_check_rejected", "sany_semantic_ok": True, "semantic_kill": False,
                "reason": "TLC rejects a constant-FALSE check before initial-state exploration"}
    completed = bool(re.search(r"Model checking completed|Finished in", text))
    nonempty = (classified.get("distinct") or 0) > 0
    if classified["status"] == "pass":
        if re.search(r"(?:^|\n)\s*(?:Error:|.*Exception|.*OutOfMemoryError|.*NoClassDefFoundError)", text):
            return {"status": "checker_diagnostic_error", "sany_semantic_ok": True, "semantic_kill": False}
        status = "holds" if tlc["returncode"] == 0 and completed and nonempty else "incomplete_or_empty_model"
        return {"status": status, "sany_semantic_ok": True, "nonempty_init": nonempty,
                "completed": completed, "distinct_states": classified.get("distinct"), "semantic_kill": False}
    violation = classified["status"] in {"invariant_violated", "property_violated"}
    # An explicit initial-state counterexample also proves Init was nonempty,
    # even when TLC stops before printing a distinct-state summary.
    nonempty = nonempty or bool(re.search(r"is violated by the initial state:\s*\n|State 1:", text))
    # Named oracle check violations establish a counterexample, not a parser/error kill.
    infrastructure_error = bool(re.search(r"OutOfMemoryError|NoClassDefFoundError|No space left|Too many open files", text))
    return {"status": "violated" if violation else classified["status"], "sany_semantic_ok": True,
            "semantic_kill": violation and nonempty and completed and not infrastructure_error,
            "nonempty_init": nonempty, "completed": completed,
            "distinct_states": classified.get("distinct"),
            "diagnostic": classified}


def resolve_dependencies(modules, reference_dir):
    """Resolve only used dependencies; reject ambiguous non-identical modules."""
    resolved = dict(modules)
    index = G._module_index()
    pending = set().union(*(G._referenced_modules(text) for text in modules.values()))
    while pending:
        name = pending.pop()
        if name in resolved or name in G.STANDARD_MODULES:
            continue
        candidates = index.get(name, [])
        preferred = [p for p in candidates if p.parent == reference_dir] or candidates
        contents = {p.read_text() for p in preferred}
        if len(contents) != 1:
            return {"status": "unresolved_dependency", "module": name, "candidate_count": len(preferred)}
        resolved[name] = contents.pop()
        pending |= G._referenced_modules(resolved[name])
    return {"status": "ready", "modules": resolved}


def execute(plan, reference_dir, java, timeout=120, dump_graph=False):
    if plan["status"] != "ready":
        return plan
    dependencies = resolve_dependencies(plan["modules"], reference_dir)
    if dependencies["status"] != "ready":
        return dependencies
    with tempfile.TemporaryDirectory(prefix="external_audit_") as tmp:
        wd = Path(tmp)
        for name, text in dependencies["modules"].items():
            (wd / f"{name}.tla").write_text(text)
        (wd / f'{plan["primary"]}.cfg').write_text(plan["cfg"])
        raw = {}
        def normalized(result):
            def clean(text):
                return text.replace(str(wd.resolve()), "<AUDIT_TMP>").replace(tmp, "<AUDIT_TMP>").replace(str(E.REPO), "<RELEASE>")
            return {"returncode": result.returncode, "stdout": clean(result.stdout), "stderr": clean(result.stderr)}
        try:
            s = subprocess.run([java, "-Xmx512m", f"-Djava.io.tmpdir={wd.resolve()}", "-cp", str(E.REPO / "tla2tools.jar"), "tla2sany.SANY", plan["primary"] + ".tla"],
                               cwd=wd, capture_output=True, text=True, timeout=60)
            raw["sany"] = normalized(s)
            if not E.strict_sany_result(raw["sany"])["passed"]:
                result = verdict(raw["sany"], None)
            else:
                command = [java, "-Xmx512m", f"-Djava.io.tmpdir={wd.resolve()}", "-XX:+UseParallelGC", "-cp", str(E.REPO / "tla2tools.jar"),
                           "tlc2.TLC", "-workers", "1", "-fp", "0", "-seed", "1", "-config", plan["primary"] + ".cfg"]
                if dump_graph:
                    command += ["-dump", "dot", "behavior.dot"]
                command += [plan["primary"] + ".tla"]
                try:
                    t = subprocess.run(command, cwd=wd, capture_output=True, text=True, timeout=timeout)
                    raw["tlc"] = normalized(t)
                    result = verdict(raw["sany"], raw["tlc"])
                except subprocess.TimeoutExpired as exc:
                    raw["timeout"] = {"limit_seconds": timeout,
                                      "partial_stdout": (exc.stdout or b"").decode(errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or ""),
                                      "partial_stderr": (exc.stderr or b"").decode(errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")}
                    raw["timeout"] = {k: v.replace(tmp, "<AUDIT_TMP>") if isinstance(v, str) else v for k, v in raw["timeout"].items()}
                    result = verdict(raw["sany"], None, timeout=True)
        except subprocess.TimeoutExpired:
            raw["sany"] = {"returncode": -1, "stdout": "", "stderr": "SANY timeout"}
            result = verdict(raw["sany"], None)
        graph = (wd / "behavior.dot").read_text() if (wd / "behavior.dot").exists() else None
        return {**result, "raw": raw, "mapping": plan.get("mapping", {}), "roots": plan.get("roots", []),
                "config_kind": plan.get("config_kind", "derived_control"), "cfg": plan["cfg"],
                "module_sha256": {n: hashlib.sha256(t.encode()).hexdigest() for n, t in dependencies["modules"].items()},
                "graph": graph if dump_graph else None}


@lru_cache(maxsize=None)
def reference_control(path_name, java, timeout):
    path = Path(path_name)
    text = path.read_text()
    name = G.module_name(text)
    plan = {"status": "ready", "modules": {name: text}, "primary": name,
            "cfg": path.with_suffix(".cfg").read_text(), "config_kind": "original_reference"}
    return execute(plan, path.parent, java, timeout)


def audit_one(job, java, timeout):
    directory = E.HERE / job["directory"]
    run = E.load(directory / "run.json")
    generated = (directory / "generation.tla").read_text()
    path = E.REPO / run["reference_path"]
    reference = path.read_text()
    cfg = path.with_suffix(".cfg").read_text()
    properties = execute(oracle_wrapper(generated, reference, cfg, "properties"), path.parent, java, timeout)
    forward = execute(oracle_wrapper(generated, reference, cfg, "behavior"), path.parent, java, timeout)
    reverse = execute(oracle_wrapper(reference, generated, cfg, "behavior"), path.parent, java, timeout)
    return {"run_id": job["run_id"], "generated_sha256": E.sha(directory / "generation.tla"),
            "reference_sha256": E.sha(path), "original_configuration_sha256": E.sha(path.with_suffix(".cfg")),
            "original_author_tlc_pass": True, "reference_self_check": reference_control(str(path), java, timeout),
            "reference_properties": properties,
            "reference_allows_generated_behaviors": forward, "generated_allows_reference_behaviors": reverse,
            "claim_scope": "Bounded reference-derived checks under explicit identity bindings; no natural-language faithfulness certification."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--java", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--max-new-outputs", type=int, help="checkpoint after a bounded batch of previously unaudited sources")
    args = parser.parse_args()
    E.verify()
    java = str(Path(args.java).resolve())
    probe = subprocess.run([java, "-version"], capture_output=True, text=True, check=True, timeout=10)
    E.require("11.0.25+9" in probe.stderr, "Use the recorded Temurin 11.0.25+9 runtime")
    E.require(1 <= args.workers <= 2 and 1 <= args.timeout <= 300, "Audit worker/time limits exceeded")
    E.require(args.max_new_outputs is None or args.max_new_outputs > 0, "Batch size must be positive")
    rows = E.collect()
    chains = {c["run_id"]: c for c in E.load(E.HERE / "provenance.json")["runs"]}
    passing = [r for r in rows if r["job"] != "smoke" and r["tlc_pass"]]
    jobs = {}
    aliases = {}
    for row in passing:
        chain = chains[row["run_id"]]
        key = (row["spec_id"], E.sha(E.HERE / chain["directory"] / "generation.tla"))
        jobs.setdefault(key, chain)
        aliases[row["run_id"]] = key
    results = {}
    script_hash = E.sha(Path(__file__))
    if args.resume and args.output.exists():
        previous = E.load(args.output)
        E.require(previous["audit_script_sha256"] == script_hash, "Cannot reuse evidence from a different evaluator")
        E.require(previous["runtime"] == probe.stderr.strip() and previous["timeout_seconds"] == args.timeout,
                  "Resume settings/runtime differ")
        for row in previous["rows"]:
            key = aliases.get(row["run_id"])
            if key is not None:
                E.require(row["generated_sha256"] == key[1], "Resumed source differs")
                results.setdefault(key, row)
    with ThreadPoolExecutor(args.workers) as pool:
        pending = [(key, chain) for key, chain in jobs.items() if key not in results]
        if args.max_new_outputs is not None:
            pending = pending[:args.max_new_outputs]
        futures = {pool.submit(audit_one, chain, java, args.timeout): key for key, chain in pending}
        for future in as_completed(futures):
            key = futures[future]
            results[key] = future.result()
            print(results[key]["run_id"], results[key]["reference_properties"]["status"],
                  results[key]["reference_allows_generated_behaviors"]["status"],
                  results[key]["generated_allows_reference_behaviors"]["status"], flush=True)
            interim = {"schema": 1, "runtime": probe.stderr.strip(), "timeout_seconds": args.timeout, "jvm_heap_MiB": 512,
                       "audit_script_sha256": script_hash, "completed_unique_outputs": len(results),
                       "expected_unique_outputs": len(jobs), "complete": len(results) == len(jobs),
                       "rows": [{**results[k], "run_id": rid, "execution_reused_from": results[k]["run_id"]}
                                for rid, k in aliases.items() if k in results]}
            args.output.write_text(json.dumps(interim, indent=2) + "\n")
    print(json.dumps({"completed_unique_outputs": len(results), "expected_unique_outputs": len(jobs),
                      "complete": len(results) == len(jobs)}), flush=True)


if __name__ == "__main__":
    main()
