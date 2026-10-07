# Evidence for the rebuttal (2026-10-07)

This folder contains the runs and analyses that the rebuttal reports and that are not in
`outputs/` or `experiments/opus45-20261004/`. All commands run from the repository root.
Every run uses the 100 evaluation specifications (`outputs/eval_100_ids.json`), the released
descriptions and the released grader (`code/analysis/grading.py`).

| Rebuttal claim | Files | Command |
|---|---|---|
| Repeated samples: Opus 19, 19, 19, 19, 17; GPT-5 5, 6, 4, 4 | `experiments/opus45-20261004/evidence/A3/`, `results/gpt-5__default__gptdesc/` | `python experiments/rebuttal-20261007/summarize.py` |
| Claude-written descriptions: Opus 31%, GPT-5 26%, open models 0% to 2% | `experiments/opus45-20261004/evidence/A2/`, `results/*__default__claudedesc/` | same |
| Opus configuration-aware rerun at 16,000 tokens: 22% | `experiments/opus45-20261004/evidence/A1/` | same |
| Description length and share of the configuration's names mentioned (205 against 99 words; 79% against 25%) | `description_coverage.json` | `python experiments/rebuttal-20261007/description_coverage.py` |
| McNemar tests and 95% bootstrap intervals | `paired_stats.json` | `python experiments/rebuttal-20261007/paired_stats.py` |
| Controls for the reference check (HourClock) | `refcheck_controls.json`, `controls/` | `python experiments/rebuttal-20261007/refcheck_controls.py` |

## Runs

| Folder under `results/` | Model | Descriptions | Setting | Outputs |
|---|---|---|---|---|
| `gpt-5__default__claudedesc` | GPT-5 (`gpt-5-2025-08-07`) | Claude-written declarative | default | 100 |
| `gpt-5__default__gptdesc` | GPT-5 (`gpt-5-2025-08-07`) | GPT-written declarative | default, samples 1 to 4 | 400 |
| `qwen2.5-coder-32b__default__claudedesc` | qwen2.5-coder:32b (Ollama) | Claude-written declarative | default | 100 |
| `llama3.3-70b__default__claudedesc` | llama3.3:70b (Ollama) | Claude-written declarative | default | 100 |
| `gpt-oss-20b__default__claudedesc` | gpt-oss:20b (Ollama) | Claude-written declarative | default | 100 |

Each folder has `results.json` (one graded record per output, with model version, token limit,
temperature and finish reason) and `generations/` (the generated modules). GPT-5 used a
16,000-token limit and the provider's default temperature, as in its released
configuration-aware run. The open models used temperature 0 and 8,192 output tokens, as in
their released configuration-aware runs, with the open-model prompt in `prompts/`. Sample 0
for GPT-5 is the released run in `outputs/gpt-5.json`.

`run_generation.py` produced these folders. For example:

    python experiments/rebuttal-20261007/run_generation.py --provider openai \
        --model-id gpt-5-2025-08-07 --label gpt-5 --mode default --desc claude --max-tokens 16000

API keys are read from environment variables. None are stored in the repository.

## Grading of the open models

The released grader requires the `---- MODULE Name ----` line. llama3.3-70b and gpt-oss-20b
often omit it, and those outputs fail SANY. All open-model numbers in this folder use the
released grader without changes.
