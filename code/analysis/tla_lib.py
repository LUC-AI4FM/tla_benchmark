"""Shared helpers for the rebuttal analyses (mutation test, reference-property check).

- parse_cfg: reads a TLC .cfg, including keywords and names on separate lines and
  (* ... *) block comments, which the July vacuity script misread.
- run_tlc_on: stages a module next to the reference's siblings exactly as
  grading.grade_clean does, runs SANY then TLC, and reports why a run
  failed (named invariant, temporal property, deadlock, error) and how many distinct
  states it found.
- module definitions: line-based split of a TLA+ module into top-level operator
  definitions, used to copy reference definitions into a generated module.
"""
from __future__ import annotations
import re, subprocess, sys, tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import grading as O
F = O   # copy_dependencies lives in grading.py
from validator import _find_java, _find_tla2tools
ROOT = O.REL

CFG_KEYWORDS = {"SPECIFICATION", "INIT", "NEXT", "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES",
                "CONSTANT", "CONSTANTS", "CONSTRAINT", "CONSTRAINTS", "ACTION_CONSTRAINT",
                "ACTION_CONSTRAINTS", "SYMMETRY", "VIEW", "CHECK_DEADLOCK", "POSTCONDITION",
                "ALIAS", "_POSSIBLE", "_PERIODIC"}
STD_MODULES = {"Naturals", "Integers", "Sequences", "FiniteSets", "TLC", "Bags", "Reals", "TLCExt",
               "SequencesExt", "FiniteSetsExt", "Functions", "Folds"}


def strip_cfg_comments(text: str) -> str:
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    return "\n".join(l.split("\\*")[0] for l in text.splitlines())


def parse_cfg(text: str) -> dict[str, list[str]]:
    """Map each cfg keyword to the names that follow it (CONSTANT assignments kept raw)."""
    out: dict[str, list[str]] = {}
    cur = None
    for line in strip_cfg_comments(text).splitlines():
        toks = line.split()
        if not toks:
            continue
        if toks[0] in CFG_KEYWORDS:
            cur = {"INVARIANTS": "INVARIANT", "PROPERTIES": "PROPERTY", "CONSTANTS": "CONSTANT",
                   "CONSTRAINTS": "CONSTRAINT"}.get(toks[0], toks[0])
            out.setdefault(cur, [])
            toks = toks[1:]
        if cur is None:
            continue
        if cur == "CONSTANT":
            if toks:
                out[cur].append(" ".join(toks))
        else:
            out[cur] += [t for t in re.split(r"[\s,]+", " ".join(toks)) if t]
    return out


def checked_names(cfg_text: str) -> dict[str, list[str]]:
    c = parse_cfg(cfg_text)
    return {"INVARIANT": c.get("INVARIANT", []), "PROPERTY": c.get("PROPERTY", [])}


_DIST = re.compile(r"([\d,]+) distinct states? found")


def classify(stdout: str, stderr: str) -> dict:
    s = stdout
    dist = None
    m = _DIST.findall(s)
    if m:
        dist = int(m[-1].replace(",", ""))
    if "No error has been found" in s:
        return {"status": "pass", "distinct": dist}
    mi = re.search(r"Error: Invariant (\S+) is violated", s)
    if mi:
        return {"status": "invariant_violated", "name": mi.group(1), "distinct": dist}
    if re.search(r"Error: Temporal properties were violated", s):
        return {"status": "property_violated", "distinct": dist}
    mp = re.search(r"Error: Property (.+?) is violated", s)
    if mp:
        return {"status": "property_violated", "name": mp.group(1)[:80], "distinct": dist}
    if re.search(r"Error: Attempted to (check equality|compare)", s):
        # the module encodes a value differently (e.g. BOOLEAN where the other uses 0..1)
        return {"status": "value_mismatch", "error": next(l for l in s.splitlines()
                                                         if l.startswith("Error:"))[:300], "distinct": dist}
    if "Parsing or semantic analysis failed" in s:
        return {"status": "parse_error", "error": "semantic analysis failed in TLC", "distinct": dist}
    ma = re.search(r"Error: Action property (\S+) .*violated", s)
    if ma:
        return {"status": "property_violated", "name": ma.group(1), "distinct": dist}
    if "Error: Deadlock reached" in s:
        return {"status": "deadlock", "distinct": dist}
    if "TLC timeout" in stderr:
        return {"status": "timeout", "distinct": dist}
    err = next((l for l in s.splitlines() if l.startswith("Error:")), "") or stderr[-200:]
    return {"status": "tlc_error", "error": err[:300], "distinct": dist}


def run_tlc_on(gen: str, ref_tla: Path, cfg_text: str, timeout: int = 120) -> dict:
    """Stage `gen` like grade_clean, run SANY and TLC with `cfg_text`, classify the result."""
    java, jar = _find_java(), _find_tla2tools()
    orig_mod = O.module_name(ref_tla.read_text(errors="replace"))
    gen_mod = O.module_name(gen) or orig_mod
    with tempfile.TemporaryDirectory(prefix="rebut_") as tmp:
        wd = Path(tmp)
        O._stage_siblings_by_module(ref_tla.parent, wd)
        (wd / f"{orig_mod}.tla").unlink(missing_ok=True)
        try:
            F.copy_dependencies(gen, ref_tla.parent, wd)
        except Exception:
            pass
        (wd / f"{gen_mod}.tla").write_text(gen)
        sany = subprocess.run([java, "-cp", jar, "tla2sany.SANY", f"{gen_mod}.tla"], cwd=wd,
                              capture_output=True, text=True, timeout=60)
        if sany.returncode != 0:
            first = next((l for l in sany.stdout.splitlines() if "rror" in l), "")
            return {"status": "parse_error", "error": first[:300]}
        (wd / f"{gen_mod}.cfg").write_text(cfg_text)
        try:
            r = subprocess.run([java, "-XX:+UseParallelGC", "-cp", jar, "tlc2.TLC", "-workers", "1",
                                "-config", f"{gen_mod}.cfg", f"{gen_mod}.tla"], cwd=wd,
                               capture_output=True, text=True, timeout=timeout)
            return classify(r.stdout, r.stderr)
        except subprocess.TimeoutExpired:
            return {"status": "timeout"}


# ---------------------------------------------------------------- module definitions

_DEF = re.compile(r"^(?:LOCAL\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*(\[[^\]]*\]|\([^)]*\))?\s*==(?!=)")
_END = re.compile(r"^(={4,}|-{4,}|THEOREM\b|ASSUME\b|ASSUMPTION\b|VARIABLES?\b|CONSTANTS?\b|EXTENDS\b|INSTANCE\b|LEMMA\b|RECURSIVE\b)")


def definitions(text: str) -> dict[str, dict]:
    """Top-level operator definitions: name -> {start, end (exclusive), text}."""
    lines = text.splitlines()
    starts = []
    for i, l in enumerate(lines):
        m = _DEF.match(l)
        if m:
            starts.append((i, m.group(1)))
    out = {}
    for k, (i, name) in enumerate(starts):
        j = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        for t in range(i + 1, j):
            if _END.match(lines[t]):
                j = t
                break
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        out.setdefault(name, {"start": i, "end": j, "text": "\n".join(lines[i:j])})
    return out


def strip_tla_comments(s: str) -> str:
    s = re.sub(r"\(\*.*?\*\)", " ", s, flags=re.S)
    return "\n".join(l.split("\\*")[0] for l in s.splitlines())


def idents(s: str) -> set[str]:
    s = re.sub(r'"[^"]*"', " ", strip_tla_comments(s))
    s = re.sub(r"([\])>])_", r"\1 ", s)   # [Next]_vars, <<A>>_vars: the subscript is a name
    s = re.sub(r"\b([WS]F)_", r"\1 ", s)   # WF_vars(A), SF_vars(A): fairness subscript
    return set(re.findall(r"(?<![\w.!])([A-Za-z_][A-Za-z0-9_]*)", s))


def closure(defs: dict[str, dict], roots: list[str]) -> list[str]:
    """Names of all definitions reachable from roots, in source order."""
    seen, stack = set(), [r for r in roots if r in defs]
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        body = defs[n]["text"].split("==", 1)[1]
        stack += [x for x in idents(body) if x in defs and x not in seen]
    return sorted(seen, key=lambda n: defs[n]["start"])


def rename(text: str, names: set[str], prefix: str) -> str:
    if not names:
        return text
    pat = re.compile(r"(?:(?<=[\])>]_)|(?<=\bWF_)|(?<=\bSF_)|(?<![\w.!]))(" + "|".join(sorted(map(re.escape, names), key=len, reverse=True)) + r")(?![\w])")
    # rename identifiers only, never inside string literals: PlusCal uses an action's name as
    # its pc label too (Lbl_1 == ... /\ pc = "Lbl_1"), and the label string must stay intact
    parts = re.split(r'("(?:[^"\\]|\\.)*")', text)
    return "".join(p if i % 2 else pat.sub(lambda m: prefix + m.group(1), p) for i, p in enumerate(parts))


def extends_of(text: str) -> list[str]:
    m = re.search(r"^EXTENDS\s+(.+?)$", text, flags=re.M)
    return [x.strip() for x in m.group(1).split(",")] if m else []


def add_extends(text: str, mods: list[str]) -> str:
    have = set(extends_of(text))
    extra = [m for m in mods if m in STD_MODULES and m not in have]
    if not extra:
        return text
    if re.search(r"^EXTENDS\s+", text, flags=re.M):
        return re.sub(r"^(EXTENDS\s+.+?)$", lambda m: m.group(1) + ", " + ", ".join(extra), text,
                      count=1, flags=re.M)
    return re.sub(r"^(-+\s*MODULE\s+\w+\s*-+\s*)$", lambda m: m.group(1) + "\nEXTENDS " + ", ".join(extra),
                  text, count=1, flags=re.M)


def append_defs(text: str, block: str) -> str:
    """Insert block before the first module's closing ==== line (a file may hold several
    modules, e.g. a spec followed by its proof module)."""
    lines = text.rstrip().splitlines()
    for i, l in enumerate(lines):
        if re.match(r"^={4,}", l):
            return "\n".join(lines[:i] + ["", block, ""] + lines[i:]) + "\n"
    return text.rstrip() + "\n\n" + block + "\n====\n"
