#!/usr/bin/env python3
"""Round-trip fidelity check for the GPT-derived JSON / NL-description layers.

Question this answers
---------------------
The `.tla` corpus is verified (SANY+TLC). The JSON extractions and the NL
`Specification` descriptions are NOT — they were produced by a single GPT pass
and never checked against ground truth. Before building a benchmark on top of
them we need a number: if we hand the JSON (and/or the description) back to a
model and ask it to rebuild the spec, how often do we recover a spec that

  (a) parses (SANY),                       -> losslessness of the representation
  (b) model-checks with the ORIGINAL cfg,  -> behavioural fidelity
  (c) keeps the original identifiers.       -> cheap structural-recall proxy

A low score means the representation is information-lossy and cannot serve as a
benchmark *input* (only as a diagnostic). A high score means it is faithful.

Conditions (ablation over what the model is given)
  json_only     : JSON only            -> tests whether the JSON alone is invertible
  nl_only       : description only      -> tests whether the NL gold is sufficient
  nl_plus_json  : description + JSON    -> the full pipeline as designed

Usage
  export OPENAI_API_KEY=sk-...
  python scripts/roundtrip_fidelity.py --n 100 --model gpt-5.5 \
         --conditions json_only nl_only nl_plus_json
  python scripts/roundtrip_fidelity.py --n 9 --dry-run    # sample only, no API

Output
  outputs/fidelity/<timestamp>/{per_spec.jsonl, reconstructions/, summary.json}
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import shutil
import sys
import tempfile
import time
from collections import defaultdict
from datetime import datetime
from difflib import SequenceMatcher
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))

from utils import get_logger, load_json  # noqa: E402
from validator import run_sany, run_tlc  # noqa: E402

logger = get_logger("fidelity")

DATA_DIR = REPO_ROOT / "data"
INDEX_PATH = DATA_DIR / "index.json"
PROMPT_DIR = REPO_ROOT / "configs" / "prompts"

CONDITIONS = ("json_only", "nl_only", "nl_plus_json")

# Pure NL->TLA prompt (the repo's nlp_* prompts all also inject JSON, which would
# defeat the nl_only ablation, so we define a JSON-free one here).
NL_ONLY_PROMPT = """You are a TLA+ specification engineer. You will receive a \
natural language description of a system. Write a complete, syntactically \
correct TLA+ specification that implements it.

Requirements:
- The output must be a valid TLA+ module that passes the SANY parser.
- Include the MODULE declaration, EXTENDS, CONSTANTS, VARIABLES, Init, Next, Spec.
- Output only the TLA+ specification, no explanation, no markdown fences.

System description:
{description}
"""

# Field whose value carries identifier names we expect to survive a faithful
# round-trip. Used for the structural-recall proxy.
NAME_FIELDS = ("ModuleName", "ConstantNames", "VariableNames", "OperatorDefNames")


# --------------------------------------------------------------------------- #
# sampling
# --------------------------------------------------------------------------- #
def load_index() -> dict[int, dict]:
    raw = load_json(INDEX_PATH)
    return {int(k): v for k, v in raw.items()}


def stratified_sample(index: dict[int, dict], n: int, tiers: list[str] | None,
                      seed: int) -> list[int]:
    """Sample n spec_ids, proportionally across complexity_tier."""
    rng = random.Random(seed)
    by_tier: dict[str, list[int]] = defaultdict(list)
    for sid, rec in index.items():
        tier = rec.get("complexity_tier", "basic")
        if tiers and tier not in tiers:
            continue
        by_tier[tier].append(sid)

    if not by_tier:
        return []

    total = sum(len(v) for v in by_tier.values())
    chosen: list[int] = []
    for tier, ids in by_tier.items():
        rng.shuffle(ids)
        k = max(1, round(n * len(ids) / total)) if n < total else len(ids)
        chosen.extend(ids[:k])
    rng.shuffle(chosen)
    return chosen[:n] if n < len(chosen) else chosen


# --------------------------------------------------------------------------- #
# model call (mirrors src/runner.py _call_openai)
# --------------------------------------------------------------------------- #
def call_model(model_name: str, prompt: str, temperature: float,
               max_tokens: int, backend: str = "openai",
               base_url: str | None = None) -> dict:
    """Call OpenAI or a local Ollama (OpenAI-compatible) endpoint.

    backend='ollama' -> base_url like http://localhost:11434/v1, free/local."""
    import openai
    if backend == "ollama":
        client = openai.OpenAI(base_url=base_url or "http://localhost:11434/v1",
                               api_key="ollama")
        token_key = "max_tokens"  # ollama compat uses max_tokens
    else:
        client = openai.OpenAI()
        token_key = "max_completion_tokens"
    kwargs: dict = {
        "model": model_name,
        "messages": [{"role": "user", "content": prompt}],
        token_key: max_tokens,
    }
    if temperature != 1:
        kwargs["temperature"] = temperature
    try:
        resp = client.chat.completions.create(**kwargs)
    except openai.BadRequestError as exc:
        # Reasoning models (gpt-5.x) reject non-default temperature; drop it.
        if "temperature" in str(exc) and "temperature" in kwargs:
            kwargs.pop("temperature")
            resp = client.chat.completions.create(**kwargs)
        else:
            raise
    choice = resp.choices[0]
    return {
        "text": choice.message.content or "",
        "tokens_in": resp.usage.prompt_tokens if resp.usage else 0,
        "tokens_out": resp.usage.completion_tokens if resp.usage else 0,
        "finish_reason": choice.finish_reason,
    }


# --------------------------------------------------------------------------- #
# prompt building + output cleaning
# --------------------------------------------------------------------------- #
def read_prompt(name: str) -> str:
    return (PROMPT_DIR / name).read_text(encoding="utf-8")


def build_prompt(condition: str, description: str, parsed_json: dict) -> str:
    json_str = json.dumps(parsed_json, indent=2, ensure_ascii=False)
    if condition == "json_only":
        return read_prompt("json_to_tla.txt").format(json_content=json_str)
    if condition == "nl_only":
        return NL_ONLY_PROMPT.format(description=description)
    if condition == "nl_plus_json":
        return read_prompt("nlp_v3_to_tla.txt").format(
            description=description, json_content=json_str)
    raise ValueError(f"unknown condition {condition!r}")


_FENCE = re.compile(r"^```[a-zA-Z]*\n?|\n?```$", re.MULTILINE)
_THINK = re.compile(r"<think>.*?</think>", re.DOTALL)
_MODULE_ANY = re.compile(r"(?:-{3,}\s*)?MODULE\s+(\w+)")
_HAS_DASHES = re.compile(r"-{3,}\s*MODULE")
_HAS_FOOTER = re.compile(r"={4,}\s*$")


def extract_tla(raw: str) -> tuple[str, str | None]:
    """Strip fences / reasoning leakage and normalise TLA+ module delimiters.

    Models often emit valid module bodies but omit the cosmetic '---- MODULE
    Name ----' header dashes and the '====' footer. Those omissions fail SANY
    for reasons unrelated to whether the description was sufficient, so we
    canonicalise them before checking. Returns (clean_text, module_name)."""
    text = _THINK.sub("", raw)
    text = _FENCE.sub("", text).strip()
    m = _MODULE_ANY.search(text)
    module_name = m.group(1) if m else None
    if m and m.start() > 0:
        text = text[m.start():]            # trim any preamble before MODULE
    if module_name and not _HAS_DASHES.search(text):
        text = re.sub(r"MODULE\s+" + re.escape(module_name),
                      f"---- MODULE {module_name} ----", text, count=1)
    if module_name and not _HAS_FOOTER.search(text):
        text = text.rstrip() + "\n" + "=" * 40
    return text, module_name


# --------------------------------------------------------------------------- #
# verification harness
# --------------------------------------------------------------------------- #
TLA_ROOT = DATA_DIR / "tla_files"


def find_cfg(tla_path: Path) -> Path | None:
    """A cfg that directly drives THIS module: same stem, else lone cfg in dir."""
    same = tla_path.with_suffix(".cfg")
    if same.exists():
        return same
    cfgs = list(tla_path.parent.glob("*.cfg"))
    return cfgs[0] if len(cfgs) == 1 else None


# Standard modules shipped inside tla2tools.jar (resolved by SANY without a file
# on disk). Exactly the StandardModules/*.tla in the jar. Anything else
# (IOUtils, CSV, TLAPS, CommunityModules, ...) must be found in the corpus.
STANDARD_MODULES = {
    "Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags", "TLC",
    "Json", "Randomization", "RealTime", "TLCExt", "Toolbox",
}
_EXTENDS = re.compile(r"^\s*EXTENDS\s+([^\n]+)", re.MULTILINE)
_INSTANCE = re.compile(r"\bINSTANCE\s+(\w+)")

_module_index: dict[str, list[Path]] | None = None


def module_index() -> dict[str, list[Path]]:
    """Map module name -> all corpus .tla files defining it (built once)."""
    global _module_index
    if _module_index is not None:
        return _module_index
    idx: dict[str, list[Path]] = defaultdict(list)
    for p in TLA_ROOT.rglob("*.tla"):
        idx[p.stem].append(p)
    _module_index = idx
    return idx


def _referenced_modules(text: str) -> set[str]:
    mods: set[str] = set()
    for m in _EXTENDS.finditer(text):
        line = m.group(1).split("\\*")[0]  # drop trailing line comment
        mods.update(x.strip() for x in line.split(",") if x.strip())
    mods.update(_INSTANCE.findall(text))
    # keep only valid TLA identifiers (guards against stray comment tokens)
    return {x for x in mods if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", x)}


def copy_dependencies(text: str, origin_dir: Path, workdir: Path) -> list[str]:
    """Recursively copy non-standard EXTENDS/INSTANCE dependency modules into the
    staging dir, to a fixpoint. Scans modules already present (siblings) too, so
    transitive deps of siblings are pulled in. Prefers the copy nearest the
    origin dir on name collisions. Returns names that could not be resolved."""
    idx = module_index()
    unresolved: list[str] = []
    scanned: set[str] = set()

    pending: set[str] = set(_referenced_modules(text))
    for f in list(workdir.glob("*.tla")):  # deps of already-staged siblings
        pending |= _referenced_modules(f.read_text(encoding="utf-8", errors="replace"))

    while pending:
        name = pending.pop()
        if name in scanned or name in STANDARD_MODULES:
            continue
        scanned.add(name)
        target = workdir / f"{name}.tla"
        if not target.exists():
            candidates = idx.get(name, [])
            if not candidates:
                unresolved.append(name)
                continue
            best = min(candidates, key=lambda p: _path_distance(origin_dir, p.parent))
            shutil.copy2(best, target)
        pending |= _referenced_modules(target.read_text(
            encoding="utf-8", errors="replace"))
    return unresolved


def _path_distance(a: Path, b: Path) -> int:
    """Tree distance between two dirs (smaller = nearer)."""
    a_parts, b_parts = a.parts, b.parts
    common = 0
    for x, y in zip(a_parts, b_parts):
        if x != y:
            break
        common += 1
    return (len(a_parts) - common) + (len(b_parts) - common)


def dependency_search_paths(original_tla: Path) -> list[str]:
    """SANY -I dirs so EXTENDS/INSTANCE of modules living outside the spec's own
    directory (shared CommunityModules, parent-level specs) still resolve.

    Walks ancestors up to data/tla_files and adds any sibling dir whose name
    looks like a shared-module location."""
    paths: list[str] = []
    try:
        rel_parts = original_tla.parent.relative_to(TLA_ROOT).parts
    except ValueError:
        return paths
    cur = TLA_ROOT
    for part in rel_parts:
        cur = cur / part
        paths.append(str(cur))
        for sib in cur.iterdir():
            if sib.is_dir() and sib.name in (
                "CommunityModules", "modules", "lib", "common", "Examples"):
                paths.append(str(sib))
    return list(dict.fromkeys(reversed(paths)))  # nearest dir first, deduped


def _copy_siblings(src_dir: Path, workdir: Path) -> None:
    """Copy sibling files (local deps, cfgs) into the staging dir; no subdirs."""
    for f in src_dir.iterdir():
        if f.is_file():
            shutil.copy2(f, workdir / f.name)


def _verify(target: Path, run_tlc_check: bool, search_paths: list[str]) -> dict:
    """Run SANY (+ TLC if a cfg drives this module) on a staged .tla file."""
    sany = run_sany(str(target), search_paths=search_paths)
    result = {
        "sany_pass": sany["passed"],
        "sany_error": "" if sany["passed"] else _first_error(sany),
        "tlc_pass": None,
        "tlc_status": "not_run",
    }
    if not run_tlc_check:
        result["tlc_status"] = "disabled"
        return result
    if not sany["passed"]:
        result["tlc_status"] = "skipped_sany_failed"
        return result
    cfg = find_cfg(target)
    if cfg is None:
        result["tlc_status"] = "no_cfg"
        return result
    tlc = run_tlc(str(target), str(cfg))
    result["tlc_pass"] = tlc["passed"]
    result["tlc_status"] = "ran"
    result["tlc_cfg"] = cfg.name
    if not tlc["passed"]:
        result["tlc_error"] = _first_error(tlc)
    return result


def verify_original(original_tla: Path, run_tlc_check: bool,
                    workdir: Path) -> dict:
    """Control: validate the UNTOUCHED original through the identical staging
    path. A reconstruction is only fairly scorable when this passes."""
    _copy_siblings(original_tla.parent, workdir)
    text = original_tla.read_text(encoding="utf-8", errors="replace")
    unresolved = copy_dependencies(text, original_tla.parent, workdir)
    # No corpus -I paths: deps are flattened into workdir by copy_dependencies.
    # Adding ancestor dirs makes SANY resolve the wrong copy of colliding modules.
    res = _verify(workdir / original_tla.name, run_tlc_check, [])
    res["unresolved_deps"] = unresolved
    return {f"original_{k}": v for k, v in res.items()}


def stage_and_verify(reconstructed: str, module_name: str | None,
                     original_tla: Path, run_tlc_check: bool,
                     workdir: Path) -> dict:
    """Write reconstructed spec into an isolated copy of the spec's directory
    (so local EXTENDS dependencies + cfg are present) and run SANY/TLC.

    Never touches the real corpus."""
    _copy_siblings(original_tla.parent, workdir)
    fname = (module_name or original_tla.stem) + ".tla"
    target = workdir / fname
    target.write_text(reconstructed, encoding="utf-8")
    copy_dependencies(reconstructed, original_tla.parent, workdir)
    result = {"staged_file": fname}
    result.update(_verify(target, run_tlc_check, []))  # deps flattened; no -I
    return result


def _first_error(res: dict) -> str:
    blob = (res.get("stdout", "") + res.get("stderr", "")).splitlines()
    for line in blob:
        if "error" in line.lower():
            return line.strip()[:300]
    return (res.get("stderr") or "")[:300]


# --------------------------------------------------------------------------- #
# cheap structural-fidelity proxies (no GPT, deterministic)
# --------------------------------------------------------------------------- #
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def expected_names(parsed_json: dict) -> set[str]:
    names: set[str] = set()
    for field in NAME_FIELDS:
        val = parsed_json.get(field)
        if isinstance(val, str):
            names.add(val)
        elif isinstance(val, list):
            names.update(x for x in val if isinstance(x, str))
    return {n for n in names if n}


def identifier_recall(reconstructed: str, expected: set[str]) -> float:
    if not expected:
        return float("nan")
    present = set(_IDENT.findall(reconstructed))
    return len(expected & present) / len(expected)


def surface_similarity(reconstructed: str, original: str) -> float:
    """Normalised similarity to the gold .tla (a contamination/copy signal)."""
    return SequenceMatcher(None, reconstructed.split(), original.split()).ratio()


# --------------------------------------------------------------------------- #
# main
# --------------------------------------------------------------------------- #
def run_one(sid: int, rec: dict, condition: str, args, out_dir: Path,
            control: dict) -> dict:
    tla_path = REPO_ROOT / rec["tla_path"]
    parsed_path = REPO_ROOT / rec["parsed_path"]
    parsed_json = load_json(parsed_path)
    description = rec.get("specification", "")
    original_text = tla_path.read_text(encoding="utf-8", errors="replace")

    row: dict = {
        "spec_id": sid,
        "module_name": rec.get("module_name"),
        "complexity_tier": rec.get("complexity_tier"),
        "condition": condition,
        "tla_path": rec["tla_path"],
    }
    row.update(control)  # original_sany_pass / original_tlc_pass / ...

    prompt = build_prompt(condition, description, parsed_json)

    if args.dry_run:
        row["status"] = "dry_run"
        return row

    t0 = time.time()
    try:
        out = call_model(args.model, prompt, args.temperature, args.max_tokens,
                         backend=args.backend, base_url=args.base_url)
    except Exception as exc:  # noqa: BLE001
        logger.error("model call failed sid=%s cond=%s: %s", sid, condition, exc)
        row["status"] = "model_error"
        row["error"] = str(exc)[:300]
        return row
    row["latency_s"] = round(time.time() - t0, 2)
    row["tokens_in"] = out["tokens_in"]
    row["tokens_out"] = out["tokens_out"]
    row["finish_reason"] = out["finish_reason"]

    reconstructed, module_name = extract_tla(out["text"])
    row["module_name_preserved"] = (module_name == rec.get("module_name"))

    # persist reconstruction for inspection
    rdir = out_dir / "reconstructions" / condition
    rdir.mkdir(parents=True, exist_ok=True)
    (rdir / f"{sid}.tla").write_text(reconstructed, encoding="utf-8")

    with tempfile.TemporaryDirectory(prefix="fidelity_") as tmp:
        verify = stage_and_verify(
            reconstructed, module_name, tla_path,
            run_tlc_check=not args.no_tlc, workdir=Path(tmp))
    row.update(verify)

    # Conditioned fidelity: only credit/blame a reconstruction when the original
    # itself passes the same gate (so missing-dependency noise is excluded).
    if control.get("original_sany_pass"):
        row["sany_fidelity"] = bool(row.get("sany_pass"))
    if control.get("original_tlc_pass") and row.get("tlc_status") == "ran":
        row["tlc_fidelity"] = bool(row.get("tlc_pass"))

    exp = expected_names(parsed_json)
    row["identifier_recall"] = round(identifier_recall(reconstructed, exp), 3)
    row["surface_similarity"] = round(surface_similarity(reconstructed, original_text), 3)
    row["status"] = "ok"
    return row


def summarize(rows: list[dict]) -> dict:
    real = [r for r in rows if r.get("status") == "ok"]
    summary: dict = {"n_attempted": len(rows), "n_scored": len(real),
                     "by_condition": {}}

    def _rate(items, key):
        vals = [r[key] for r in items if r.get(key) is not None]
        return round(sum(bool(v) for v in vals) / len(vals), 3) if vals else None

    def _mean(items, key):
        vals = [r[key] for r in items
                if isinstance(r.get(key), (int, float)) and r[key] == r[key]]
        return round(sum(vals) / len(vals), 3) if vals else None

    # Control: how many originals pass our harness (the fair denominator).
    by_spec = {r["spec_id"]: r for r in real}.values()
    summary["control"] = {
        "original_sany_pass_rate": _rate(list(by_spec), "original_sany_pass"),
        "original_tlc_pass_rate_where_run": _rate(
            [r for r in by_spec if r.get("original_tlc_status") == "ran"],
            "original_tlc_pass"),
    }

    for cond in CONDITIONS:
        c = [r for r in real if r["condition"] == cond]
        if not c:
            continue
        tlc_ran = [r for r in c if r.get("tlc_status") == "ran"]
        sany_cond = [r for r in c if "sany_fidelity" in r]
        tlc_cond = [r for r in c if "tlc_fidelity" in r]
        summary["by_condition"][cond] = {
            "n": len(c),
            # headline: fidelity conditioned on the original passing the gate
            "sany_fidelity": _rate(sany_cond, "sany_fidelity"),
            "n_sany_fidelity": len(sany_cond),
            "tlc_fidelity": _rate(tlc_cond, "tlc_fidelity"),
            "n_tlc_fidelity": len(tlc_cond),
            # raw (unconditioned) rates for reference
            "sany_pass_rate_raw": _rate(c, "sany_pass"),
            "tlc_pass_rate_raw_where_run": _rate(tlc_ran, "tlc_pass"),
            "n_tlc_runs": len(tlc_ran),
            "module_name_preserved_rate": _rate(c, "module_name_preserved"),
            "mean_identifier_recall": _mean(c, "identifier_recall"),
            "mean_surface_similarity": _mean(c, "surface_similarity"),
            "mean_tokens_out": _mean(c, "tokens_out"),
        }

    # per-tier SANY breakdown (the headline losslessness signal)
    tiers: dict = defaultdict(lambda: defaultdict(list))
    for r in real:
        tiers[r["complexity_tier"]][r["condition"]].append(r["sany_pass"])
    summary["sany_pass_by_tier"] = {
        tier: {cond: round(sum(v) / len(v), 3) for cond, v in conds.items()}
        for tier, conds in tiers.items()
    }
    return summary


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=100, help="number of specs to sample")
    ap.add_argument("--conditions", nargs="+", default=list(CONDITIONS),
                    choices=CONDITIONS)
    ap.add_argument("--model", default="gpt-5.5", help="model name (OpenAI or Ollama tag)")
    ap.add_argument("--backend", default="openai", choices=["openai", "ollama"])
    ap.add_argument("--base-url", default=None, help="Ollama base url, e.g. http://localhost:11434/v1")
    ap.add_argument("--ids-file", default=None, help="JSON list of spec_ids to restrict to (e.g. gold set)")
    ap.add_argument("--temperature", type=float, default=0.0)
    ap.add_argument("--max-tokens", type=int, default=32768)
    ap.add_argument("--tiers", nargs="+", default=None,
                    help="restrict to these complexity tiers")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--no-tlc", action="store_true",
                    help="SANY only; skip TLC model checking")
    ap.add_argument("--dry-run", action="store_true",
                    help="sample + build prompts but make no API calls")
    ap.add_argument("--out", default=None, help="output dir (default: timestamped)")
    args = ap.parse_args()

    if (not args.dry_run and args.backend == "openai"
            and not os.environ.get("OPENAI_API_KEY")):
        ap.error("OPENAI_API_KEY not set. `export OPENAI_API_KEY=sk-...`, "
                 "use --backend ollama, or --dry-run.")

    index = load_index()
    if args.ids_file:
        wanted = set(load_json(args.ids_file))
        index = {sid: rec for sid, rec in index.items() if sid in wanted}
        logger.info("restricted to %d specs from %s", len(index), args.ids_file)
    sample = stratified_sample(index, args.n, args.tiers, args.seed)
    logger.info("sampled %d specs (seed=%d) across conditions=%s",
                len(sample), args.seed, args.conditions)

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    out_dir = Path(args.out) if args.out else (
        REPO_ROOT / "outputs" / "fidelity" / stamp)
    out_dir.mkdir(parents=True, exist_ok=True)
    logger.info("writing results to %s", out_dir)

    rows: list[dict] = []
    per_spec_path = out_dir / "per_spec.jsonl"
    with per_spec_path.open("w", encoding="utf-8") as fh:
        for i, sid in enumerate(sample, 1):
            rec = index[sid]
            # Control: validate the untouched original ONCE per spec.
            control: dict = {}
            if not args.dry_run:
                tla_path = REPO_ROOT / rec["tla_path"]
                with tempfile.TemporaryDirectory(prefix="fidelity_ctrl_") as tmp:
                    control = verify_original(
                        tla_path, run_tlc_check=not args.no_tlc, workdir=Path(tmp))
                logger.info("[%d/%d] sid=%s control: original_sany=%s original_tlc=%s",
                            i, len(sample), sid, control.get("original_sany_pass"),
                            control.get("original_tlc_pass"))
            for cond in args.conditions:
                logger.info("[%d/%d] sid=%s tier=%s cond=%s",
                            i, len(sample), sid, rec.get("complexity_tier"), cond)
                row = run_one(sid, rec, cond, args, out_dir, control)
                rows.append(row)
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
                fh.flush()

    summary = summarize(rows)
    summary["config"] = {
        "model": args.model, "n_requested": args.n, "n_sampled": len(sample),
        "conditions": args.conditions, "tiers": args.tiers, "seed": args.seed,
        "tlc_enabled": not args.no_tlc, "dry_run": args.dry_run,
    }
    (out_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")

    print("\n=== ROUND-TRIP FIDELITY SUMMARY ===")
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    print(f"\nPer-spec rows: {per_spec_path}")
    print(f"Reconstructions: {out_dir / 'reconstructions'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
