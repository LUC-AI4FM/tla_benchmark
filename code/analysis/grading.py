"""Grading helpers shared by the analysis scripts (release layout).

This is the grader used for every configuration-aware and pass-quality result:
  - the generated module keeps its own module name and is staged next to every other
    gold module (each under its real module name, as SANY requires)
  - modules it EXTENDS or INSTANCEs are resolved among the released specifications
  - SANY parses it; TLC then runs it with the reference configuration

It mirrors opus_contamination_rerun.grade_clean in the project repository. The only
difference is where imported modules are looked up: the project repository searched its
raw corpus, the release searches the 1,300 released specifications. check_grading.py
re-grades every released output with this file and compares the verdicts.
"""
from __future__ import annotations
import re
import shutil
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

REL = Path(__file__).resolve().parents[2]          # the release root
sys.path.insert(0, str(REL / "code"))
from validator import run_sany, run_tlc  # noqa: E402

GOLD = REL / "specs" / "gold"
SPECS = REL / "specs"
STANDARD_MODULES = {"Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags", "TLC",
                    "Json", "Randomization", "RealTime", "TLCExt", "Toolbox"}
_EXTENDS = re.compile(r"^\s*EXTENDS\s+([^\n]+)", re.MULTILINE)
_INSTANCE = re.compile(r"\bINSTANCE\s+(\w+)")

# the generation prompts (identical to the ones used for the released outputs)
GEN_PROMPT = (
    "You are a TLA+ specification engineer. You will receive a natural language "
    "description of a system. Produce a complete, syntactically correct TLA+ "
    "specification that faithfully captures the described behavior. The output must be "
    "a valid TLA+ module that passes the SANY parser. Include the MODULE declaration, "
    "EXTENDS, CONSTANTS, VARIABLES, Init, Next and Spec. Include all safety invariants "
    "and liveness properties described, and any fairness conditions mentioned. Output "
    "only the TLA+ specification.\n\nSystem description: {description}"
)
GEN_PROMPT_CFG = (
    "You are a TLA+ specification engineer. You will receive a natural language "
    "description of a system and the exact names your specification must define so that "
    "it binds to a fixed model-checking configuration. Produce a complete, syntactically "
    "correct TLA+ specification that faithfully captures the described behavior and defines "
    "exactly the named constants, variables, and operators listed below. The output must be "
    "a valid TLA+ module that passes the SANY parser. Output only the TLA+ specification.\n\n"
    "System description: {description}\n\n"
    "Your module MUST define these names so the configuration binds: {names}"
)


def gold_paths(spec_id: str):
    tlas = list(GOLD.glob(f"{spec_id}_*.tla"))
    if not tlas:
        return None, None
    tla = tlas[0]
    cfg = tla.with_suffix(".cfg")
    return tla, (cfg if cfg.exists() else None)


def extract_module(text: str) -> str:
    m = re.search(r"-{3,}\s*MODULE.*?={4,}", text, re.DOTALL)
    return m.group(0) if m else text


def module_name(text: str):
    m = re.search(r"-{3,}\s*MODULE\s+(\w+)", text)   # TLA+ module names may start with a digit
    return m.group(1) if m else None


def cfg_names(cfg_text: str) -> str:
    """The identifiers a cfg references; supplied to the model in the config-aware regime."""
    names = []
    for line in cfg_text.splitlines():
        line = line.split("\\*")[0]
        m = re.match(r"\s*(SPECIFICATION|INIT|NEXT|INVARIANT[S]?|PROPERT(?:Y|IES))\s+(.*)", line)
        if m:
            names += [t for t in re.split(r"[\s,]+", m.group(2).strip()) if t]
        m2 = re.match(r"\s*CONSTANT[S]?\s+(.*)", line)
        if m2:
            for tok in re.split(r"[\s,]+", m2.group(1).strip()):
                if re.match(r"^[A-Za-z_]\w*$", tok):
                    names.append(tok)
    seen, out = set(), []
    for x in names:
        if x not in seen:
            seen.add(x); out.append(x)
    return ", ".join(out)


def _stage_siblings_by_module(src_dir: Path, wd: Path) -> None:
    """Copy every sibling .tla (and its .cfg) into wd under its real module name."""
    for f in src_dir.glob("*.tla"):
        txt = f.read_text(errors="replace")
        mn = module_name(txt)
        if not mn:
            continue
        (wd / f"{mn}.tla").write_text(txt)
        c = f.with_suffix(".cfg")
        if c.exists():
            (wd / f"{mn}.cfg").write_text(c.read_text(errors="replace"))


_index: dict[str, list[Path]] | None = None


def _module_index() -> dict[str, list[Path]]:
    global _index
    if _index is None:
        idx: dict[str, list[Path]] = defaultdict(list)
        for p in SPECS.rglob("*.tla"):
            mn = module_name(p.read_text(errors="replace"))
            if mn:
                idx[mn].append(p)
        _index = idx
    return _index


def _referenced_modules(text: str) -> set[str]:
    mods: set[str] = set()
    for m in _EXTENDS.finditer(text):
        mods.update(x.strip() for x in m.group(1).split("\\*")[0].split(",") if x.strip())
    mods.update(_INSTANCE.findall(text))
    return {x for x in mods if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", x)}


def copy_dependencies(text: str, origin_dir: Path, workdir: Path) -> list[str]:
    """Copy imported non-standard modules (transitively) into the staging dir."""
    idx = _module_index()
    unresolved, scanned = [], set()
    pending = set(_referenced_modules(text))
    for f in list(workdir.glob("*.tla")):
        pending |= _referenced_modules(f.read_text(errors="replace"))
    while pending:
        name = pending.pop()
        if name in scanned or name in STANDARD_MODULES:
            continue
        scanned.add(name)
        target = workdir / f"{name}.tla"
        if not target.exists():
            cands = idx.get(name, [])
            if not cands:
                unresolved.append(name)
                continue
            best = sorted(cands, key=lambda p: (p.parent != origin_dir, str(p)))[0]
            shutil.copy2(best, target)
        pending |= _referenced_modules(target.read_text(errors="replace"))
    return unresolved


def grade_clean(gen: str, tla_path: Path) -> dict:
    """SANY then TLC with the reference configuration, as the paper describes."""
    orig_mod = module_name(tla_path.read_text(errors="replace"))
    gen_mod = module_name(gen) or orig_mod
    cfg_path = tla_path.with_suffix(".cfg")
    with tempfile.TemporaryDirectory(prefix="grade_") as tmp:
        wd = Path(tmp)
        _stage_siblings_by_module(tla_path.parent, wd)
        (wd / f"{orig_mod}.tla").unlink(missing_ok=True)
        copy_dependencies(gen, tla_path.parent, wd)
        target = wd / f"{gen_mod}.tla"
        target.write_text(gen)
        sany = run_sany(str(target), search_paths=[])
        if not sany["passed"]:
            return {"sany_pass": False, "tlc_pass": False}
        if not cfg_path.exists():
            return {"sany_pass": True, "tlc_pass": False}
        (wd / f"{gen_mod}.cfg").write_text(cfg_path.read_text(errors="replace"))
        tlc = run_tlc(str(target), str(wd / f"{gen_mod}.cfg"))
        return {"sany_pass": True, "tlc_pass": bool(tlc["passed"])}
