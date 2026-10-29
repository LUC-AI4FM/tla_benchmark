"""Build experiments/benchmark-v2/tasks.jsonl: one line per benchmark specification (Gold A).

Each line holds what a model run needs and nothing from the upstream modules themselves:
  spec_id, module (the reference's module name), the four English descriptions, and `names`,
  the identifiers that the configuration-aware prompt lists. For a record with its own
  configuration (or a model from the upstream manifest that belongs to it), `names` are the
  identifiers its .cfg uses, read across lines (the earlier
  runs read one line at a time and missed names listed on the lines after a keyword). For a record checked through a wrapper
  module, `names` are the identifiers that the wrapper module and its .cfg use and that the
  record itself declares or defines, because those are the names the generated module must
  provide for the wrapper to bind.

Run from the repository root (needs dataset/ and the audit results):
    python experiments/benchmark-v2/build_tasks.py <benchmark ids JSON>                    # Gold A -> tasks.jsonl
    python experiments/benchmark-v2/build_tasks.py <{id: "A"|"B"} JSON> gold_tasks.jsonl   # all gold, with a tier field
"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "code" / "analysis"))
import grading as G
import tla_lib as R

DATA = ROOT / "dataset"
SETS = ["declarative_gpt", "declarative_claude", "intent_gpt", "intent_claude"]
rows = {r["spec_id"]: r for r in map(json.loads, open(DATA / "manifest.jsonl"))}
aud_file = ROOT / "outputs/audit/dataset_audit_upstream.partial.jsonl"
audit = {json.loads(l)["spec_id"]: json.loads(l) for l in open(aud_file)}
ids = json.load(open(sys.argv[1]))
tier_of = json.load(open(sys.argv[3])) if len(sys.argv) > 3 else {}      # optional {spec_id: "A" | "B"}
if isinstance(ids, dict):
    tier_of, ids = ids, sorted(ids, key=int)


KEYS = {"SPECIFICATION", "INIT", "NEXT", "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES", "CONSTANT",
        "CONSTANTS", "SYMMETRY", "VIEW", "CONSTRAINT", "CONSTRAINTS", "ACTION_CONSTRAINT", "ACTION_CONSTRAINTS",
        "ALIAS", "POSTCONDITION", "CHECK_DEADLOCK"}


def cfg_names(cfg_text):
    """Every identifier a .cfg refers to in the specification, across lines: the operators named in each
    section and, in CONSTANT sections, each constant and each operator substituted with <-
    (model values on the right of = are not names of the module)."""
    text = re.sub(r"\(\*.*?\*\)", " ", cfg_text, flags=re.S)
    text = re.sub(r"\\\*[^\n]*", " ", text)
    toks = re.findall(r"<-|=|[A-Za-z_]\w*|\S", text)
    names, section, i = [], None, 0
    while i < len(toks):
        t = toks[i]
        if t in KEYS:
            section = t
        elif section in ("CONSTANT", "CONSTANTS") and re.fullmatch(r"[A-Za-z_]\w*", t):
            nxt = toks[i + 1] if i + 1 < len(toks) else ""
            if nxt in ("=", "<-"):
                names.append(t)
                if nxt == "<-" and i + 2 < len(toks) and re.fullmatch(r"[A-Za-z_]\w*", toks[i + 2]):
                    names.append(toks[i + 2])
                i += 2
                if nxt == "=":                          # skip the value up to the next constant or section
                    depth = 0
                    while i < len(toks) and not (depth == 0 and (toks[i] in KEYS or
                            (re.fullmatch(r"[A-Za-z_]\w*", toks[i]) and i + 1 < len(toks) and toks[i + 1] in ("=", "<-")))):
                        depth += toks[i] in "{(<[" ; depth -= toks[i] in "})>]"
                        i += 1
                    continue
        elif section and section not in ("CONSTANT", "CONSTANTS", "CHECK_DEADLOCK") and re.fullmatch(r"[A-Za-z_]\w*", t):
            names.append(t)
        i += 1
    seen, out = set(), []
    for n in names:
        if n not in seen and n not in ("TRUE", "FALSE"):
            seen.add(n); out.append(n)
    return ", ".join(out)


def declared(text):
    """Constants, variables and operator definitions of a module."""
    t = R.strip_tla_comments(text)
    names = set(R.definitions(text))
    # operator definitions whose parameters contain nested parentheses, e.g. Reduce(op(_, _), x)
    names |= set(re.findall(r"(?m)^\s*(?:LOCAL\s+|RECURSIVE\s+)?([A-Za-z_]\w*)\s*\(.*?==", t))
    for kw in ("CONSTANTS?", "VARIABLES?"):
        for m in re.finditer(rf"(?m)^\s*{kw}\s+([^\n]+)", t):
            names |= {re.sub(r"\(.*", "", x).strip() for x in m.group(1).split(",")}
    return {n for n in names if re.fullmatch(r"[A-Za-z_]\w*", n)}


out = []
for sid in ids:
    row, a = rows[sid], audit[sid]
    ref = (DATA / row["path"]).read_text(errors="replace")
    cfg = DATA / a["config"]
    if a["config_source"] == "wrapper":
        wrapper = cfg.with_suffix(".tla").read_text(errors="replace")
        used = set(re.findall(r"[A-Za-z_]\w*", R.strip_tla_comments(wrapper) + "\n" + cfg.read_text(errors="replace")))
        names = ", ".join(sorted(used & declared(ref)))
    else:
        names = cfg_names(cfg.read_text(errors="replace"))
    descs = {s: (DATA / row["descriptions"][s]).read_text(encoding="utf-8").strip() for s in SETS}
    extra = {"tier": "gold_" + tier_of[sid].lower()} if tier_of else {}
    out.append({"spec_id": sid, "module": G.module_name(ref), **extra, "names": names,
                **{f"desc_{s}": descs[s] for s in SETS}})
dest = ROOT / "experiments" / "benchmark-v2" / (sys.argv[2] if len(sys.argv) > 2 else "tasks.jsonl")
dest.write_text("".join(json.dumps(x) + "\n" for x in out))
print("tasks:", len(out), " checked through a wrapper:", sum(audit[s]["config_source"] == "wrapper" for s in ids),
      " empty names:", sum(not x["names"] for x in out))
