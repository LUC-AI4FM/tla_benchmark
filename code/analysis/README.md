# Analysis scripts

These scripts produce every file under `outputs/` that is not a raw model output. Run them
from the release root. They need Python 3.10+, Java 11+ and `tla2tools.jar` (included at the
release root). Results are written to `outputs/rerun/`, so they can be compared with the
released files without overwriting them.

| Script | Produces | What it does |
|---|---|---|
| `grading.py` | (library) | The grader: stages the generated module next to the gold modules, runs SANY, then TLC with the reference configuration. Also holds the two generation prompts. |
| `check_grading.py` | (report) | Re-grades all 900 released generated specifications and compares each verdict with the released one. |
| `check_gold_parse.py` | `rerun/gold_parse.json` | Parses all 403 gold references with SANY exactly as the grader stages them, to confirm every import resolves inside the release. |
| `fixture_audit.py` | `audit/fixture_audit.json` | Model-checks every evaluation reference and records its number of distinct states. |
| `mutation_test.py` | `pass_quality/mutation_*.json` | Behavior-mutation test. `--regime default` (the 30 default passes), `reference` (the reference specifications), `control` (real properties against a vacuous one), `cfgaware`. |
| `reference_check.py` | `pass_quality/refcheck_default.json` | Checks each pass against the reference: the reference's own property definitions, and TLC refinement in both directions under the identity mapping on variable names. |
| `audit_undecided.py` | `pass_quality/audit12.json` | The 12 passes the reference check could not decide, re-checked with an explicit mapping for each (renamed PlusCal labels, boolean versus 0/1 encoding, `RECURSIVE` declarations, `INIT`/`NEXT` configurations, extended modules). |
| `tla_lib.py` | (library) | Configuration parser, TLC runner that reports why a run failed, and the definition-copying used by the two checks above. |

Examples:

```
python code/analysis/check_grading.py
python code/analysis/mutation_test.py --regime default
python code/analysis/reference_check.py --regime default
python code/analysis/audit_undecided.py
```

TLC verdicts are deterministic. Run times depend on the machine; the slowest references
take several minutes each.
