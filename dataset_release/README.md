# TLA+ Specification Benchmark (Internal Release)

Internal share of the cleaned, execution-grounded TLA+ benchmark. This copy
includes the raw specifications. It is for internal use within the group only, not
for public redistribution (the specs come from 9 source repos with their own
licenses). The public version ships pointers instead of raw specs.

## What is in this folder

```
manifest.jsonl            One row per spec. The index that ties everything together.
specs/
  gold/                   403 specs that parse (SANY) and model-check (TLC). Each .tla
                          plus its .cfg where available. File name is <spec_id>_<name>.tla.
  silver/                 897 specs that parse only (no runnable config).
descriptions/
  declarative_gpt/        Translation-style descriptions, GPT. Names leak so TLC grades exactly.
  declarative_claude/     Translation-style descriptions, Claude.
  intent/                 Design-style descriptions. Names hidden. Graded parse-only.
  perturbed/              Descriptions with the perturbation renaming applied (111).
perturbation/
  perturb_gold_system.json  Rename maps and verified flags. 111 of 146 system specs
                            stay valid after semantics-preserving renaming. This is
                            the contamination test set.
docs/
  DATASET_CARD.md         One-page dataset summary (provenance, counts, structure).
  construction_provenance.json  How the corpus was cleaned (drop counts, decision rule).
  results_tables.md       Baseline and frontier results.
  construct_failure_map.md  Where models fail, by TLA+ construct.
  figures/                Plots (pass@k curves, SANY by tier and model).
```

## Counts

- 403 gold (146 system, 257 utility), 897 silver. 1,300 total.
- 111 perturbation-verified specs (the contamination test set).
- Descriptions: 1,614 GPT declarative, 306 Claude declarative, 134 intent, 111 perturbed.

## manifest.jsonl fields

Each row: `spec_id`, `tier` (gold/silver), `category` (system/utility, gold only),
`complexity` (basic/intermediate/advanced), `source_repo`, `source_repo_url`,
`source_path`, `spec_sha256`, the description fields, and the perturbation fields
(`perturbed_verified`, `rename_map`, `desc_perturbed`).

To find a spec file from a manifest row, look in `specs/<tier>/` for a file
starting with `<spec_id>_`.

## How grading works

A model is given a description and must output a TLA+ module. We stage it with its
dependencies and run SANY (parser), then TLC (model checker) bound to the gold
config by the original spec name. Gold tier is graded on TLC (behavioral
correctness); silver and intent are graded SANY-only.

## Source repositories

tlaplus, microsoft, Azure, pingcap, apalache-mc, atomix, tendermint, josehu07,
TeamTilapia.

## Note

This release reflects the dataset as of 2026-06-27. The perturbation set may grow
slightly (we are recovering a few specs that failed renaming), and a human-verified
description subset is planned.
