from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Optional

sys.path.insert(0, str(Path(__file__).parent))

from utils import (
    data_dir, get_logger, load_json, load_text, outputs_dir,
    repo_root, results_dir, save_json,
)

logger = get_logger("analyzer")

TAXONOMY: dict[str, dict[str, str]] = {
    "SYNTACTIC": {
        "unicode_substitution": "Unicode operators instead of ASCII",
        "missing_module_header": "No ---- MODULE Name ---- header",
        "missing_module_footer": "No ==== footer",
        "duplicate_module_header": "Multiple MODULE declarations",
        "cross_language_injection": "Foreign language syntax",
        "reasoning_leakage": "<think> tags in output",
        "undefined_operator": "Uses undefined operator",
        "undeclared_variable": "Uses undeclared variable",
        "malformed_expression": "Other SANY parse error",
        "encoding_error": "Non-ASCII encoding issues",
    },
    "SEMANTIC": {
        "invariant_violation": "TLC invariant violation",
        "deadlock": "TLC deadlock",
        "type_error": "TLC type mismatch",
        "config_mismatch": "Spec/cfg mismatch",
        "state_explosion": "TLC timeout",
        "liveness_violation": "Liveness check failed",
    },
    "STRUCTURAL": {
        "empty_specification": "Trivially empty Init/Next",
        "missing_safety_properties": "No invariants defined",
        "missing_liveness": "No fairness/temporal properties",
        "excessive_length": ">2x reference LOC",
    },
    "GENERATION": {
        "no_tla_block": "No extractable TLA+ module",
        "truncated_output": "Output cut off mid-spec",
        "multiple_modules": "More than one MODULE block",
        "hallucinated_imports": "EXTENDS non-existent modules",
    },
}

_UNICODE_OPS = re.compile(r"[∧∨¬⇒⇔∀∃□◇↝∈∉≜≡≤≥≠⊆∪∩×]")
_FOREIGN_SYNTAX = re.compile(r"(?:^|\s)(?:class |def |import |from |public |private |void |int |return )|[;{}]|```", re.MULTILINE)
_THINK_LEAK = re.compile(r"<think>|</think>|<\|thinking\|>|<\|/thinking\|>", re.IGNORECASE)
_MODULE_HEADER = re.compile(r"-{4,}\s*MODULE\s+\w+\s*-{4,}")
_MODULE_FOOTER = re.compile(r"={4,}")
_EXTENDS_LINE = re.compile(r"EXTENDS\s+([\w\s,]+)")

_VALID_STD_MODULES: set[str] = {
    "Naturals", "Integers", "Reals", "Sequences", "FiniteSets",
    "Bags", "TLC", "TLAPS", "TLCExt", "Json", "IOUtils",
    "Randomization", "Toolbox", "Apalache",
}

_TLC_INVARIANT = re.compile(r"Invariant .+ is violated", re.IGNORECASE)
_TLC_DEADLOCK = re.compile(r"deadlock reached", re.IGNORECASE)
_TLC_TYPE_ERROR = re.compile(r"Attempted to .+ non-.+ value|type mismatch|IllegalArgumentException", re.IGNORECASE)
_TLC_LIVENESS = re.compile(r"Temporal properties were violated|liveness checking failed", re.IGNORECASE)
_TLC_TIMEOUT = re.compile(r"TLC timeout|state space exploration incomplete", re.IGNORECASE)


def classify_syntactic(sany_stdout: str, sany_stderr: str, tla_source: Optional[str]) -> dict[str, bool]:
    combined = sany_stdout + "\n" + sany_stderr
    source = tla_source or ""

    results: dict[str, bool] = {}
    results["unicode_substitution"] = bool(_UNICODE_OPS.search(source))
    results["missing_module_header"] = not bool(_MODULE_HEADER.search(source))
    results["missing_module_footer"] = not bool(_MODULE_FOOTER.search(source))
    results["duplicate_module_header"] = len(_MODULE_HEADER.findall(source)) > 1
    results["cross_language_injection"] = bool(_FOREIGN_SYNTAX.search(source))
    results["reasoning_leakage"] = bool(_THINK_LEAK.search(source))
    results["undefined_operator"] = "Unknown operator" in combined or "not defined" in combined.lower()
    results["undeclared_variable"] = "Unknown variable" in combined or "not declared" in combined.lower()
    results["encoding_error"] = any(
        ord(c) > 127 and c not in "∧∨¬⇒⇔∀∃□◇↝∈∉≜≡≤≥≠⊆∪∩×"
        for c in source
    )
    known_flags = any(results.values())
    results["malformed_expression"] = not known_flags and bool(combined.strip())
    return results


def classify_semantic(tlc_stdout: str, tlc_stderr: str) -> dict[str, bool]:
    combined = tlc_stdout + "\n" + tlc_stderr
    return {
        "invariant_violation": bool(_TLC_INVARIANT.search(combined)),
        "deadlock": bool(_TLC_DEADLOCK.search(combined)),
        "type_error": bool(_TLC_TYPE_ERROR.search(combined)),
        "config_mismatch": "does not match" in combined.lower() or "not found" in combined.lower(),
        "state_explosion": bool(_TLC_TIMEOUT.search(combined)) or "TLC timeout" in combined,
        "liveness_violation": bool(_TLC_LIVENESS.search(combined)),
    }


def classify_structural(tla_source: str, reference_source: Optional[str] = None) -> dict[str, bool]:
    results: dict[str, bool] = {}

    init_match = re.search(r"Init\s*==\s*(.+?)(?:\n|$)", tla_source)
    results["empty_specification"] = bool(
        init_match and init_match.group(1).strip() in ("TRUE", "FALSE", "TRUE /\\ TRUE")
    )

    has_invariant = bool(
        re.search(r"Inv\w*\s*==", tla_source) or
        re.search(r"TypeInvariant\s*==", tla_source, re.IGNORECASE) or
        re.search(r"INVARIANT", tla_source, re.IGNORECASE)
    )
    results["missing_safety_properties"] = not has_invariant

    has_liveness = bool(
        re.search(r"WF_|SF_|<>|~>|\[\]<>", tla_source) or
        re.search(r"Fairness|Liveness", tla_source, re.IGNORECASE)
    )
    results["missing_liveness"] = not has_liveness

    if reference_source:
        gen_loc = len([l for l in tla_source.splitlines() if l.strip()])
        ref_loc = max(len([l for l in reference_source.splitlines() if l.strip()]), 1)
        results["excessive_length"] = gen_loc > 2 * ref_loc
    else:
        results["excessive_length"] = False

    return results


def classify_generation(raw_response: str, tla_source: Optional[str]) -> dict[str, bool]:
    results: dict[str, bool] = {}
    results["no_tla_block"] = tla_source is None

    if tla_source is not None:
        results["truncated_output"] = not bool(_MODULE_FOOTER.search(tla_source))
    else:
        results["truncated_output"] = bool(raw_response) and "MODULE" in raw_response

    if tla_source is not None:
        results["multiple_modules"] = len(_MODULE_HEADER.findall(tla_source)) > 1
    else:
        results["multiple_modules"] = len(_MODULE_HEADER.findall(raw_response)) > 1

    source = tla_source or raw_response
    extends_match = _EXTENDS_LINE.search(source)
    if extends_match:
        imported = {m.strip() for m in extends_match.group(1).split(",")}
        results["hallucinated_imports"] = len(imported - _VALID_STD_MODULES) > 0
    else:
        results["hallucinated_imports"] = False

    return results


def classify_sample(
    raw_response: str,
    tla_source: Optional[str],
    sany_pass: bool,
    tlc_pass: bool,
    sany_stdout: str = "",
    sany_stderr: str = "",
    tlc_stdout: str = "",
    tlc_stderr: str = "",
    reference_source: Optional[str] = None,
) -> dict[str, Any]:
    all_flags: dict[str, bool] = {}

    gen_flags = classify_generation(raw_response, tla_source)
    all_flags.update({f"generation.{k}": v for k, v in gen_flags.items()})

    if tla_source is None:
        primary = "GENERATION"
    elif not sany_pass:
        primary = "SYNTACTIC"
        syn_flags = classify_syntactic(sany_stdout, sany_stderr, tla_source)
        all_flags.update({f"syntactic.{k}": v for k, v in syn_flags.items()})
    elif not tlc_pass:
        primary = "SEMANTIC"
        sem_flags = classify_semantic(tlc_stdout, tlc_stderr)
        all_flags.update({f"semantic.{k}": v for k, v in sem_flags.items()})
    else:
        primary = "STRUCTURAL"
        struct_flags = classify_structural(tla_source, reference_source)
        all_flags.update({f"structural.{k}": v for k, v in struct_flags.items()})

    triggered = [k for k, v in all_flags.items() if v]

    return {
        "primary_domain": primary,
        "sub_categories": triggered,
        "is_correct": sany_pass and tlc_pass,
        **all_flags,
    }


def analyze_all_outputs() -> list[dict[str, Any]]:
    validation_base = outputs_dir() / "validation"
    extracted_base = outputs_dir() / "extracted"
    raw_base = outputs_dir() / "raw"

    if not validation_base.exists():
        logger.error("No validation outputs at %s", validation_base)
        return []

    records: list[dict[str, Any]] = []

    for model_dir in sorted(validation_base.iterdir()):
        if not model_dir.is_dir():
            continue
        model_id = model_dir.name

        for cond_dir in sorted(model_dir.iterdir()):
            if not cond_dir.is_dir():
                continue
            condition = cond_dir.name

            for spec_dir in sorted(cond_dir.iterdir()):
                if not spec_dir.is_dir():
                    continue
                spec_id = spec_dir.name

                ref_path = data_dir() / "tla_files" / f"{spec_id}.tla"
                reference_source = load_text(ref_path) if ref_path.exists() else None

                for summary_file in sorted(spec_dir.glob("*_summary.json")):
                    summary = load_json(summary_file)
                    sample_name = summary_file.stem.replace("_summary", "")

                    sany_file = spec_dir / f"{sample_name}_sany.json"
                    sany_data = load_json(sany_file) if sany_file.exists() else {}

                    tlc_file = spec_dir / f"{sample_name}_tlc.json"
                    tlc_data = load_json(tlc_file) if tlc_file.exists() else {}

                    tla_file = extracted_base / model_id / condition / spec_id / f"{sample_name}.tla"
                    tla_source = load_text(tla_file) if tla_file.exists() else None

                    raw_file = raw_base / model_id / condition / spec_id / f"{sample_name}.json"
                    raw_response = ""
                    if raw_file.exists():
                        raw_data = load_json(raw_file)
                        raw_response = raw_data.get("response_text", "")

                    classification = classify_sample(
                        raw_response=raw_response, tla_source=tla_source,
                        sany_pass=summary.get("sany_pass", False),
                        tlc_pass=summary.get("tlc_pass", False),
                        sany_stdout=sany_data.get("stdout", ""),
                        sany_stderr=sany_data.get("stderr", ""),
                        tlc_stdout=tlc_data.get("stdout", ""),
                        tlc_stderr=tlc_data.get("stderr", ""),
                        reference_source=reference_source,
                    )

                    record = {
                        "model_id": model_id, "condition": condition,
                        "spec_id": spec_id, "sample": sample_name,
                        **classification,
                    }
                    records.append(record)

        logger.info("analyzed  model=%s  samples=%d", model_id, len(records))

    return records


def build_hivemind_heatmap(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    model_failures: dict[str, list[dict]] = defaultdict(list)
    for r in records:
        if not r.get("is_correct", False):
            model_failures[r["model_id"]].append(r)

    all_subcats: set[str] = set()
    for domain_cats in TAXONOMY.values():
        for subcat in domain_cats:
            for domain_name in TAXONOMY:
                all_subcats.add(f"{domain_name.lower()}.{subcat}")

    heatmap_rows: list[dict[str, Any]] = []
    for model_id, failures in sorted(model_failures.items()):
        total = max(len(failures), 1)
        row: dict[str, Any] = {"model_id": model_id, "total_failures": len(failures)}

        for subcat_key in sorted(all_subcats):
            count = sum(1 for f in failures if f.get(subcat_key, False))
            row[subcat_key] = round(100 * count / total, 1)

        heatmap_rows.append(row)

    return heatmap_rows


def main() -> None:
    parser = argparse.ArgumentParser(description="TLA+Bench error taxonomy analyzer.")
    parser.parse_args()

    records = analyze_all_outputs()
    if not records:
        logger.warning("No records to analyse.")
        return

    output_dir = results_dir() / "analysis"
    output_dir.mkdir(parents=True, exist_ok=True)

    csv_records = []
    for r in records:
        flat = {k: v for k, v in r.items() if k != "sub_categories"}
        flat["sub_categories"] = ";".join(r.get("sub_categories", []))
        csv_records.append(flat)

    fieldnames = list(csv_records[0].keys())
    agg_path = output_dir / "aggregate_taxonomy.csv"
    with open(agg_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(csv_records)
    logger.info("wrote %d records to %s", len(csv_records), agg_path)

    heatmap = build_hivemind_heatmap(records)
    if heatmap:
        hm_fields = list(heatmap[0].keys())
        hm_path = output_dir / "hivemind_heatmap.csv"
        with open(hm_path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=hm_fields)
            writer.writeheader()
            writer.writerows(heatmap)
        logger.info("wrote hivemind heatmap to %s", hm_path)

    from itertools import groupby

    csv_records.sort(key=lambda r: (r["model_id"], r.get("condition", "")))
    for (mid, cond), group in groupby(csv_records, key=lambda r: (r["model_id"], r.get("condition", ""))):
        rows = list(group)
        per_path = output_dir / f"{mid}_{cond}_taxonomy.csv"
        with open(per_path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)

    logger.info("analysis complete")


if __name__ == "__main__":
    main()
