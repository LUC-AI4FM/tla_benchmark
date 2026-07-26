# TLA+-Bench

TLA+-Bench is a dataset for going from a natural-language description to a TLA+
specification. It contains 1,300 TLA+ specifications collected from 13 public
repositories across 9 GitHub organizations. Every specification comes with
natural-language descriptions written by two language models in two styles.

## What is in this folder

The `specs` folder holds the specifications. The `gold` subfolder has 403
specifications that both parse under SANY and model-check under TLC; each gold
specification has a `.tla` file and a matching `.cfg` configuration. The `silver`
subfolder has 897 specifications that parse under SANY but do not ship a runnable
configuration. Files are named `<id>_<Module>.tla`.

The `descriptions` folder holds four sets of natural-language descriptions, one text
file per specification, keyed by the specification id. The `declarative` sets keep the
module's real names. The `intent` sets hide the names and describe only what the system
should do. Each style was written by two providers, GPT-5 and Claude Opus 4.5, giving
`declarative_gpt`, `declarative_claude`, `intent_gpt`, and `intent_claude`.

The file `manifest.jsonl` has one JSON record per specification, one record per line.
The file `manifest.json` has the same records as a single JSON array. `LICENSE` covers
licensing and responsible use.

## Manifest fields

Each record gives the specification id, the tier (gold or silver), a category (system or
utility, for gold specifications), a difficulty label (basic, intermediate, or advanced),
the source repository and its URL, the path the specification came from, the SHA-256 of
the released `.tla` file, and the natural-language descriptions.

## Code, grading tools, and reproduction

The `code` folder holds the exact grader used in the paper. `code/validator.py`
runs the SANY parse gate and the TLC semantic gate over a specification and its
reference configuration, with the compute budget the paper states; `tla2tools.jar`
is included. See `code/README.md` for usage.

The `outputs` folder holds the graded model verdicts behind the reported tables:
the per-model results on the 100-specification evaluation set
(`claude-opus-4-5.json`, `gemini-2-5-pro.json`, `gpt-5.json`), the open-model
results (`outputs/contamination/*__clean.json`), and the pass-quality and vacuity
records (`_pass_audit.json`, `all_passes_vacuity.json`, `oracle_scope_proof.json`).

Running

```
python reproduce.py
```

recomputes Table 5, the correctness envelope of Table 6, and the pass-quality
counts of Section 8.7 from these verdicts, with no model queries. To re-grade a
generated specification from scratch, use `code/validator.py`.

## Licensing and responsible use

The `.tla` specifications come from 13 public repositories; each specification's source
repository, URL, and path are recorded in the manifest, and the original licenses of those
repositories apply. The descriptions and the manifest annotations are released under
CC BY 4.0. See `LICENSE`.

Please do not train on this dataset. It is meant for evaluation, and training on it would
defeat its purpose.
