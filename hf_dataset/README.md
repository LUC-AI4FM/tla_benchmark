---
license: other
license_name: mixed-source-see-readme
task_categories:
  - text-generation
language:
  - en
tags:
  - formal-methods
  - tla-plus
  - specification
  - model-checking
  - code-generation
  - contamination
  - memorization
pretty_name: TLA+ Execution-Grounded Specification Benchmark
size_categories:
  - 1K<n<10K
configs:
  - config_name: default
    data_files: specs.jsonl
---

# TLA+ Execution-Grounded Specification Benchmark

A benchmark for evaluating LLM generation of TLA+ formal specifications, graded by
the model checker (SANY parser plus TLC model checker), not by text similarity. It
also ships a semantics-preserving perturbation set for contamination-controlled
evaluation (measuring memorization versus real derivation).

NOTE: This dataset distributes our annotations plus pointers to the original
specs. It does NOT redistribute the raw .tla source files, because they were
collected from 9 separate GitHub repositories with their own licenses. Use
`fetch_specs.py` to reconstruct the spec files from local clones of the source
repos. See Licensing below.

## What is in here

`specs.jsonl` has one row per spec. Fields:

- `spec_id`: stable integer id.
- `tier`: `gold` (parses with SANY and passes TLC model checking) or `silver`
  (parses with SANY only, no runnable config).
- `category`: `system` or `utility` (gold only), assigned by a 3-model vote.
- `complexity`: `basic`, `intermediate`, or `advanced`.
- `source_repo`, `source_repo_url`, `source_path`: where the original spec came
  from. Used by `fetch_specs.py` to reconstruct the file.
- `spec_sha256`: first 16 hex chars of the SHA-256 of the original spec file, so
  you can detect if a source file has drifted from the version we used.
- `desc_declarative_gpt`, `desc_declarative_claude`: natural-language descriptions
  in the declarative (translation) style, from two providers.
- `desc_intent`: a description in the intent (design) style, which hides operator
  and constant names.
- `perturbed_verified`: true if this spec stays valid (parses and model-checks)
  after semantics-preserving renaming. These form the contamination test set.
- `rename_map`: the identifier renaming applied for the perturbed variant.
- `desc_perturbed`: the description with the same renaming applied.

## Counts

- 403 gold specs (146 system, 257 utility).
- 897 silver specs.
- 111 perturbation-verified specs (the contamination test set).

## Source repositories

tlaplus, microsoft, Azure, pingcap, apalache-mc, atomix, tendermint, josehu07,
TeamTilapia. See `source_repo_url` per row.

## How to reconstruct the spec files

```
python fetch_specs.py --clones /path/to/your/repo/clones
```

Clone the source repos listed in `source_repo_url`, point `--clones` at them, and
the script copies the matching files into `tla_files/` and verifies each against
`spec_sha256`.

## How grading works

A model is given a description and must output a TLA+ module. The module is graded
by staging it with its dependencies and running:

1. SANY (parser). If it does not parse, it fails.
2. TLC (model checker), bound to the gold config by the original spec name. If it
   does not model-check, it fails. Gold tier only.

The declarative track leaks operator and constant names, so the gold config binds
and TLC grades exact behavioral correctness. The intent track hides names, so it
is graded SANY-only for now.

## Contamination / memorization use

The perturbation set renames every user identifier (module, constants, variables,
operators) consistently across the spec, its config, and dependent modules, then
re-verifies with SANY and TLC. A model that memorized the public spec fails the
renamed version, while a model that genuinely derives the spec still passes. The
gap between clean and perturbed correctness measures memorization.

## Licensing

The annotations in `specs.jsonl` (labels, descriptions, perturbations, scores) are
released under CC BY 4.0. The original .tla specifications are NOT included and
remain under the licenses of their respective source repositories. You must obtain
them from the source repos, whose licenses govern their use. `fetch_specs.py` does
not bundle them; it copies from clones you provide.

## Citation

To be added on publication.
