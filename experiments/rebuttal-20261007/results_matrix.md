# Results matrix

Correct outputs out of the 100 evaluation items (TLC pass). One run per cell unless noted. "not run" marks a combination without a run. Gemini-2.5-pro is no longer offered to new API users, so its new combinations were not run.

| Model | Default: GPT-written declarative | Default: Claude-written declarative | Default: intent (GPT) | Default: intent (Claude) | Config-aware: GPT-written declarative | Config-aware: Claude-written declarative | Config-aware: intent (GPT) | Config-aware: intent (Claude) |
|---|---|---|---|---|---|---|---|---|
| Claude Opus 4.5 | 16 (paper) | 31 | 3 | 7 | 26 | 32 | 13 | 21 |
| Gemini-2.5-pro | 10 (paper) | not run | not run | not run | 22 | not run | not run | not run |
| GPT-5 | 4 (paper) | 26 | 0 | 1 | 28 | 36 | 6 | 23 |
| qwen2.5-coder-32b | 1 (paper) | 2 | 0 | 0 | 2 | 0 | 0 | 1 |
| llama3.3-70b | 0 (paper) | 0 | 0 | 0 | 1 | 3 | 1 | 1 |
| gpt-oss-20b | 1 (paper) | 1 | 0 | 0 | 4 | 5 | 4 | 3 |

## Repeated runs (default setting, GPT-written declarative descriptions)

| Model | Paper run | New runs | Solved by at least one new run |
|---|---|---|---|
| Claude Opus 4.5 | 16 | 19, 19, 19, 19, 17 (5 new runs, A3) | 27 |
| GPT-5 | 4 | 5, 6, 4, 4 (4 new runs, B2) | 13 |
| qwen2.5-coder-32b | 1 | 0, 0, 1, 0, 0 (5 runs at temperature 0.8) | 1 |
| llama3.3-70b | 0 | 0, 0, 0, 0, 0 (5 runs at temperature 0.8) | 0 |
| gpt-oss-20b | 1 | 3, 3, 3, 1, 2 (5 runs at temperature 0.8) | 10 |

## Other reruns

| Run | Correct out of 100 | Files |
|---|---|---|
| Claude Opus 4.5, configuration-aware, GPT-written declarative, 16,000 tokens (A1) | 22 | `experiments/opus45-20261004/evidence/A1/` |
| qwen2.5-coder-32b, default, GPT-written declarative, rerun with the released grader (D0) | 1 | `results/qwen2.5-coder-32b__default__gptdesc/` |
| llama3.3-70b, default, GPT-written declarative, rerun with the released grader (D0) | 0 | `results/llama3.3-70b__default__gptdesc/` |
| gpt-oss-20b, default, GPT-written declarative, rerun with the released grader (D0) | 0 | `results/gpt-oss-20b__default__gptdesc/` |

## Notes

- The configuration-aware GPT-written column is the released run in `outputs/cfgaware/`. The Claude Opus 4.5 value there (26) used a 4,096-token limit. The A1 rerun at 16,000 tokens gave 22.
- New open-model runs are graded with the released grader (`code/analysis/grading.py`), which requires the `---- MODULE Name ----` line. llama3.3-70b and gpt-oss-20b often omit it in the default setting.
- The paper's default-setting values for the open models come from `outputs/contamination/`.
- The temperature 0.8 open-model runs have five samples of which sample 0 is not the paper's run.
