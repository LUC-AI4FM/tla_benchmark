# New results after the reviews (October 2026)

This folder contains every model run and analysis made after the reviews that is not in
`outputs/` or `experiments/opus45-20261004/`. All commands run from the repository root.
Every run uses the 100 evaluation items (`outputs/eval_100_ids.json`), the descriptions in
`descriptions/` and the grader in `code/analysis/grading.py`.

**Start with `results_matrix.md`.** It lists the number of correct outputs for every model,
description set and setting, with the paper's values next to the new ones. Recompute it with
`python experiments/rebuttal-20261007/results_matrix.py`.

## Analyses

| Result | Files | Command |
|---|---|---|
| Full results matrix | `results_matrix.md` | `python experiments/rebuttal-20261007/results_matrix.py` |
| Repeated runs and second description provider | `results/`, `experiments/opus45-20261004/evidence/` | `python experiments/rebuttal-20261007/summarize.py` |
| Description length and share of the configuration's names mentioned (205 against 99 words; 79% against 25%) | `description_coverage.json` | `python experiments/rebuttal-20261007/description_coverage.py` |
| McNemar tests and 95% bootstrap intervals | `paired_stats.json` | `python experiments/rebuttal-20261007/paired_stats.py` |
| Controls for the reference comparison (HourClock) | `refcheck_controls.json`, `controls/` | `python experiments/rebuttal-20261007/refcheck_controls.py` |

The reference comparison, the behavior-change test and their controls for the 30 correct
outputs are in `outputs/pass_quality/`, produced by `code/analysis/reference_check.py`,
`code/analysis/audit_undecided.py` and `code/analysis/mutation_test.py`.

## Runs in `results/`

Folder names follow `<model>__<setting>__<descriptions>desc`. Settings: `default` (description
only) and `cfgaware` (description and the names the reference configuration uses).
Descriptions: `gpt` and `claude` (declarative, written by GPT-5 or Claude) and `intent_gpt` and
`intent_claude` (intent style, which hides the module's names).

| Model | Runs | Settings |
|---|---|---|
| Claude Opus 4.5 (`claude-opus-4-5`) | Claude-written declarative; both intent sets | configuration-aware; intent sets also default |
| GPT-5 (`gpt-5`) | Claude-written declarative; both intent sets; 4 repeated runs on GPT-written declarative | both settings |
| qwen2.5-coder-32b, llama3.3-70b, gpt-oss-20b | GPT-written declarative (rerun); Claude-written declarative; both intent sets; 5 runs at temperature 0.8 | both settings |

Each folder has `results.json` (one graded record per output, with model version, token limit,
temperature and finish reason) and `generations/` (the generated modules).

Settings used:

- **Claude Opus 4.5:** Amazon Bedrock `us.anthropic.claude-opus-4-5-20251101-v1:0`, 16,000
  output tokens, the provider's default temperature. Run by Eric Spencer. Request and grading
  records are in `opus_provenance/`. The intent runs were first made on the `paid-runs` branch
  and copied here unchanged (`opus_provenance/reuse_provenance/`).
- **GPT-5:** `gpt-5-2025-08-07`, 16,000 output tokens, the provider's default temperature
  (GPT-5 accepts no temperature setting). Sample 0 of the repeated runs is the paper's run in
  `outputs/gpt-5.json`.
- **Open models:** Ollama, temperature 0 (or 0.8 for the repeated runs), 8,192 output tokens,
  with the open-model prompt in `prompts/` for the default setting.
- **Gemini-2.5-pro:** no new runs. Google's API no longer offers this model to new users.

The Claude Opus 4.5 runs on the GPT-written declarative descriptions (A1, A2, A3) are in
`experiments/opus45-20261004/`.

## Grading of the open models

The grader requires the `---- MODULE Name ----` line. llama3.3-70b and gpt-oss-20b often omit it
in the default setting, and those outputs fail SANY. All new open-model numbers use the grader
without changes.

## Rerunning a job

`run_generation.py` produced the GPT-5 and open-model folders. For example:

    python experiments/rebuttal-20261007/run_generation.py --provider openai \
        --model-id gpt-5-2025-08-07 --label gpt-5 --mode default --desc claude --max-tokens 16000

API keys are read from environment variables. None are stored in the repository.
