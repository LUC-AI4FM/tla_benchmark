#!/usr/bin/env python3
"""Audit of the 12 default-regime passes that reference_check.py could not decide.

The automatic two-way refinement check (reference_check.py) uses the identity mapping on
variable names. For 12 of the 30 passing outputs it gave no verdict, for mechanical reasons.
This script states each reason and removes it explicitly, then re-runs the same two TLC checks:

  forward  the reference specification, as a property of the generated specification
  reverse  the generated specification, as a property of the reference specification

Per-case adjustments (each one is a refinement mapping or a fix to the copy step):
  label     PlusCal pc labels renamed; the copied formula maps the label strings
  encoding  booleans used where the reference uses 0/1; the copied formula maps
            x <-> (IF x THEN 1 ELSE 0) and x <-> (x = 1)
  recursive the copied definitions include their RECURSIVE declaration
  initnext  the configuration names INIT/NEXT instead of a SPECIFICATION; both sides get
            Spec == Init /\\ [][Next]_vars built from those operators
  extends   the reference takes HC from the module it EXTENDS; that module's definitions
            are added to the reference text before copying

Writes outputs/rebuttal/audit12.json.
"""
from __future__ import annotations
import json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tla_lib as R
from reference_check import rewrite_cfg, verdict

ROOT = R.ROOT
GEN = lambda m, s: ROOT / f"outputs/generations/default/{m}/{s}.tla"
OPUS, GEMINI, GPT5 = "claude-opus-4-5", "gemini-2-5-pro", "gpt-5"
BOOL = {"fwd": {"rdy": "(IF rdy THEN 1 ELSE 0)", "ack": "(IF ack THEN 1 ELSE 0)"},
        "rev": {"rdy": "(rdy = 1)", "ack": "(ack = 1)"}}

CASES = [
    (GPT5, "528", "label", {"str_fwd": {"Lbl_1": "Start"}, "str_rev": {"Start": "Lbl_1"}}),
    (OPUS, "1595", "label", {"str_fwd": {"Lbl_1": "loop"}, "str_rev": {"loop": "Lbl_1"}}),
    (GEMINI, "1588", "label", {"str_fwd": {"lp": "E", "a": "E"}, "str_rev": {"E": "lp"}}),
    (GEMINI, "891", "encoding", {"id_fwd": BOOL["fwd"], "id_rev": BOOL["rev"]}),
    (GPT5, "891", "encoding", {"id_fwd": BOOL["fwd"], "id_rev": BOOL["rev"]}),
    (OPUS, "1501", "recursive", {}),
    (GEMINI, "1501", "recursive", {}),
    (OPUS, "928", "extends", {"ref_extends": "HourClock"}),
    (GEMINI, "928", "extends", {"ref_extends": "HourClock"}),
    (OPUS, "1503", "initnext", {}),
    (GEMINI, "1503", "initnext", {}),
    (OPUS, "1504", "initnext", {}),
]


def sub_strings(text, mapping):
    for a, b in mapping.items():
        text = text.replace(f'"{a}"', f'"{b}"')
    return text


def sub_idents(text, mapping):
    if not mapping:
        return text
    pat = re.compile(r"(?<![\w.!\"])(" + "|".join(map(re.escape, mapping)) + r")(?![\w\"])")
    parts = re.split(r'("(?:[^"\\]|\\.)*")', text)
    return "".join(p if i % 2 else pat.sub(lambda m: mapping[m.group(1)], p) for i, p in enumerate(parts))


def copy_defs(target, source, roots, prefix, str_map=None, id_map=None):
    """import_defs of reference_check, plus RECURSIVE declarations and explicit mappings."""
    sdefs = R.definitions(source)
    names = R.closure(sdefs, roots)
    block = "\n\n".join(R.rename(sdefs[n]["text"], set(names), prefix) for n in names)
    rec = [prefix + n for line in source.splitlines() if line.strip().startswith("RECURSIVE")
           for n in re.findall(r"([A-Za-z_]\w*)\s*\(", line) if n in names]
    if rec:
        block = "RECURSIVE " + ", ".join(f"{r}(_)" for r in rec) + "\n" + block
    block = sub_idents(sub_strings(block, str_map or {}), id_map or {})
    out = R.add_extends(target, R.extends_of(source))
    return R.append_defs(out, f"\\* ---- copied for the audit ({prefix}*) ----\n" + block), \
        {n: prefix + n for n in names}


def add_spec(text, cfg):
    """Spec == Init /\\ [][Next]_vars from the cfg's INIT/NEXT names."""
    c = R.parse_cfg(cfg)
    init, nxt = c["INIT"][0], c["NEXT"][0]
    var_line = re.search(r"^VARIABLES?\s+(.+?)$", text, flags=re.M).group(1)
    vs = ", ".join(v.strip() for v in var_line.split(",") if v.strip())
    return R.append_defs(text, f"AuditSpec == {init} /\\ [][{nxt}]_<<{vs}>>"), "AuditSpec"


def run(model, sid, kind, opt):
    tla, cfg = R.O.gold_paths(sid)
    ref, gen = tla.read_text(errors="replace"), GEN(model, sid).read_text(errors="replace")
    cfg_text = cfg.read_text(errors="replace")
    c = R.parse_cfg(cfg_text)
    spec = c.get("SPECIFICATION", [None])[0]
    if "ref_extends" in opt:
        base = (tla.parent / f"{tla.name.split('_', 1)[0]}_{opt['ref_extends']}.tla")
        base = base if base.exists() else next(tla.parent.glob(f"*_{opt['ref_extends']}.tla"))
        base_defs = "\n\n".join(d["text"] for d in R.definitions(base.read_text()).values())
        # the extended module's definitions are needed only as a source to copy from; the
        # module that is checked keeps its EXTENDS and is not modified
        ref_src = R.append_defs(ref, base_defs)
        gen_src = R.append_defs(gen, base_defs) if opt["ref_extends"] in R.extends_of(gen) else gen
    if kind == "initnext":
        ref, spec = add_spec(ref, cfg_text)
        gen, _ = add_spec(gen, cfg_text)
    base_cfg = "\n".join(l for l in rewrite_cfg(cfg_text, False, {}).splitlines()
                         if not l.startswith(("INIT", "NEXT", "SPECIFICATION")))
    model_line = f"SPECIFICATION {spec}\n"

    ref_src = locals().get("ref_src", ref)
    gen_src = locals().get("gen_src", gen)
    g2, mp = copy_defs(gen, ref_src, [spec], "REF_", opt.get("str_fwd"), opt.get("id_fwd"))
    fwd = R.run_tlc_on(g2, tla, base_cfg + "\n" + model_line + f"PROPERTY {mp[spec]}\n", timeout=180)
    r2, mp = copy_defs(ref, gen_src, [spec], "GEN_", opt.get("str_rev"), opt.get("id_rev"))
    rev = R.run_tlc_on(r2, tla, base_cfg + "\n" + model_line + f"PROPERTY {mp[spec]}\n", timeout=180)
    f, r = verdict(fwd, behavior=True), verdict(rev, behavior=True)
    behavior = ("same_behaviors" if f == r == "holds" else
                "omits_reference_behavior" if f == "holds" and r == "violated" else
                "adds_behavior" if f == "violated" and r == "holds" else
                "differs_both_ways" if f == r == "violated" else "undecided")
    return {"model": model, "spec_id": sid, "adjustment": kind, "mapping": opt,
            "forward": f, "forward_tlc": fwd, "reverse": r, "reverse_tlc": rev, "behavior": behavior}


def main() -> int:
    recs = [run(*c) for c in CASES]
    dest = ROOT / "outputs/rerun"; dest.mkdir(parents=True, exist_ok=True)
    json.dump(recs, open(dest / "audit12.json", "w"), indent=2)
    for r in recs:
        print(f"  {r['model']:16s} {r['spec_id']:5s} {r['adjustment']:9s} fwd={r['forward']:15s} "
              f"rev={r['reverse']:15s} -> {r['behavior']}"
              + ("" if r["behavior"] != "undecided" else
                 f"   [{(r['forward_tlc'].get('error') or '')[:60]} | {(r['reverse_tlc'].get('error') or '')[:60]}]"))
    from collections import Counter
    print("summary:", dict(Counter(r["behavior"] for r in recs)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
