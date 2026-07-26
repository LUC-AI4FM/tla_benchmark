# Code and grading tools

This folder holds the exact grader used in the paper and the model-query scripts
that produced the descriptions.

## Grading a specification

`validator.py` grades a generated `.tla` against a reference `.cfg` with the two
gates the paper defines:

1. **Validity gate** — `run_sany(tla_path)` runs the SANY parser. A specification
   that does not parse is invalid.
2. **Semantic gate** — `run_tlc(tla_path, cfg_path)` runs the TLC model checker
   over the full reachable state space of the reference configuration. A run with
   no violation passes.

A specification is **correct** when it passes both gates. The grader runs TLC with
a single worker at the Java default heap, a 300-second TLC time limit and a
60-second SANY limit, and deadlock checking left at its TLC default. These are the
budgets stated in the reproducibility appendix; the resource-limit outcome depends
on them, so results on much slower hardware or a smaller heap may differ for the
memory-bounded cases.

### Requirements

- Java (JDK 11+) on `PATH` (https://adoptium.net)
- `tla2tools.jar` in the repository root (already included)

### Example

```python
from validator import run_sany, run_tlc

sany = run_sany("MySpec.tla")
if sany["passed"]:
    tlc = run_tlc("MySpec.tla", "MySpec.cfg")
    print("correct" if tlc["passed"] else "fails semantic gate")
else:
    print("invalid TLA+")
```

## Reproducing the tables

From the repository root:

```
python reproduce.py
```

This recomputes Table 5, the correctness envelope of Table 6, and the pass-quality
counts of Section 8.7 from the released verdicts in `outputs/`, without querying any
model.

## Generation scripts

`generation/` holds the scripts that queried the models for the descriptions. They
read the provider API key from the environment (`ANTHROPIC_API_KEY`,
`OPENAI_API_KEY`); no key is stored in the repository. They are included for
transparency and are not needed to reproduce the graded results, since the
descriptions and outputs are released directly.
