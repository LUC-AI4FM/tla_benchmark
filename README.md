# TLA+-Bench

TLA+-Bench is a dataset for going from a natural-language description to a TLA+
specification. It contains 1,300 TLA+ specifications collected from 13 public
repositories across 9 GitHub organizations. Every specification comes with
natural-language descriptions written by two language models in two styles.

## What is in this folder

The `specs` folder holds the specifications. The `gold` subfolder has 403
specifications that both parse under SANY and model-check under TLC; each gold
specification has a `.tla` file and a matching `.cfg` configuration, except four
listed in `outputs/audit/gold_without_cfg.json` (see CHANGES below). The `silver`
subfolder has 897 specifications that parse under SANY but do not ship a runnable
configuration. The `deps` subfolder holds two modules that are not benchmark items; they are
included only so that imports resolve (see `specs/deps/README.md`). Files are named `<id>_<Module>.tla`.

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

The `outputs` folder holds everything behind the reported tables:

| Path | Contents |
|---|---|
| `eval_100_ids.json` | the 100 evaluation specifications |
| `claude-opus-4-5.json`, `gemini-2-5-pro.json`, `gpt-5.json` | graded default-regime results |
| `contamination/*__clean.json` | graded default-regime results of the three open models |
| `cfgaware/*.json` | graded configuration-aware results of all six models |
| `generations/default/<model>/<id>.tla` | the generated specifications of the frontier models, default regime |
| `generations/cfgaware/<model>/<id>.tla` | the generated specifications of all six models, configuration-aware regime |
| `pass_quality/mutation_default.json` | behavior-mutation test on every default-regime pass, per mutant |
| `pass_quality/mutation_reference.json` | the same test on the reference specifications |
| `pass_quality/mutation_control.json` | control: real properties against a vacuous one |
| `pass_quality/refcheck_default.json` | each pass checked against the reference (properties and behaviors) |
| `pass_quality/audit12.json` | the 12 passes the reference check could not decide, re-checked with explicit mappings |
| `audit/fixture_audit.json` | distinct-state count of every evaluation reference |
| `audit/gold_without_cfg.json` | gold specifications with no configuration |
| `_pass_audit.json` | per-pass audit used for the substantive-pass count |

Running

```
python reproduce.py
```

recomputes Table 6, Table A7, Table A4, Table A6, the correctness envelope of Table 5,
and the pass-quality counts of Section 8.7 on the 100 evaluation specifications. Every
number is counted from the files above, with no model queries. `python reproduce.py
--clean` also prints each table without the specifications listed under Evaluation set in
CHANGES.
To re-grade a generated specification from scratch, use `code/validator.py`. The scripts
that produce the pass-quality, audit and configuration-aware files are in `code/analysis/`
(see `code/analysis/README.md`); `code/analysis/check_grading.py` re-grades all 900
released generated specifications and compares them with the released verdicts.

The default-regime generated specifications of the open models are not included; their
graded results are. The generation prompts are in `code/generation/` and in the paper's appendix.

## CHANGES

This release corrects the reviewer release of July 2026. The previous `reproduce.py` is
kept as `reproduce_as_submitted.py`.

- **Configuration-aware results.** The previous script printed the configuration-aware
  row of the envelope as a fixed value (56 of 300). Only the Claude Opus 4.5 run behind it
  existed. We ran GPT-5 (snapshot `gpt-5-2025-08-07`) and Gemini-2.5-pro in this regime on
  the same 100 specifications with the same prompt, names, and grader as the Opus run.
  The correct rates are Opus 26%, GPT-5 28%, Gemini 22%, pooled 76 of 300. The open-model
  values in the submitted Table A7 also had no run behind them. Measured with the same
  prompt and grader, they are qwen2.5-coder-32b 2%, llama3.3-70b 1% and gpt-oss-20b 4%.
  The open models use their default-regime decoding settings (Ollama, temperature 0.0,
  8,192 output tokens); llama3.3-70b used a 12,288-token context so that it fits on one
  GPU, which holds the prompt and the full output.
- **Mutation test.** The previous test replaced each checked invariant with `TRUE`. That
  cannot make a passing run fail, so it cannot show that a property is vacuous, and the
  previous script printed its count as a fixed value. It is replaced by a behavior-mutation
  test: the specification's actions are mutated one change at a time and TLC is re-run with
  the original configuration. A property is load-bearing when it catches a mutant that
  changes the reachable behavior. A control with a vacuous property is included.
- **Reference check.** New. Each pass is checked against the reference module: the
  reference's own definitions of the configured properties, and TLC refinement in both
  directions. The 12 passes this cannot decide under the identity mapping are re-checked
  with explicit mappings. Of the 30 passes, 27 match the reference behavior exactly, 2 miss
  some reference behavior and 1 implements a different algorithm.
- **Evaluation set.** Specification 1142 has no usable configuration (its source Toolbox
  model is empty), and six references (1275, 1343, 1413, 1435, 1455, 1504) have a single
  reachable state. They remain in the 100-specification evaluation set and are flagged in
  `outputs/audit/`; `python reproduce.py --clean` also reports every table without them.
- **Gold tier.** Specifications 853, 854, 1140, and 1142 are labelled gold but have no
  configuration of their own.
- **Grader in the release.** `code/analysis/grading.py` resolves imported modules among the
  released specifications. `code/analysis/check_grading.py` re-grades all 900 released
  generated specifications with it and reproduces every released verdict, apart from the
  random item below. `code/analysis/check_gold_parse.py` confirms that all 403 gold
  references parse in the release layout.
- **Known limitation.** The July Opus configuration-aware run used a 4,096-token budget;
  the other runs used 16,000. Two Opus outputs (1009, 1578) reached that limit; both failed.
- **Known limitation.** Specification 875 (`SpanTreeRandom`) uses TLC's `RandomElement`, so
  TLC checks a different random graph on each run. The reference passes on every run. The
  Opus configuration-aware output passed in the released run; on re-runs it took between
  21 and 301 seconds and failed once by reaching the 300-second limit.

## Supplementary Opus 4.5 runs (2026-10-04)

The [new evidence release](experiments/opus45-20261004/README.md) adds 600 experimental
outputs with exact prompts, configurations, dependencies, and raw grading evidence.
It reports diagnostic-aware SANY results separately from the retained historical flags,
verified 300-second TLC nonpasses, matched A3 pass@4, and explicitly uncertified mixed
baseline coverage. It preserves the historical tables above. Reproduce the supplement
offline with `python3 experiments/opus45-20261004/reproduce.py --check`.

## Licensing and responsible use

The `.tla` specifications come from 13 public repositories; each specification's source
repository, URL, and path are recorded in the manifest, and the original licenses of those
repositories apply. The descriptions and the manifest annotations are released under
CC BY 4.0. See `LICENSE`.

Please do not train on this dataset. It is meant for evaluation, and training on it would
defeat its purpose.
