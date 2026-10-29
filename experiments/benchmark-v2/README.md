# Benchmark v2: model runs

The benchmark is the Gold A tier of the rebuilt dataset: 232 specifications that pass TLC in their
upstream folder, reach more than one state, draw no random values, check a named property and come
from an example folder. `tasks.jsonl` holds one line per specification with what a run needs:

| Field | Content |
|---|---|
| `spec_id` | Record number of the dataset |
| `module` | Module name of the reference |
| `desc_declarative_gpt`, `desc_declarative_claude`, `desc_intent_gpt`, `desc_intent_claude` | The four English descriptions |
| `names` | Names that the configuration-aware prompt lists (read across all lines of the configuration) |

Runs only generate. Grading happens afterwards with the dataset's grader, which checks each module in
its upstream folder.

## Jobs per model

Eight jobs: the default and configuration-aware settings for each of the four description sets. Job 1
runs five samples per specification, which gives the repeated runs.

| Job | `--mode` | `--desc` | `--samples` | `--sample-offset` |
|---|---|---|---|---|
| 1 | default | gpt | 5 | 0 |
| 2 | cfgaware | gpt | 1 | 0 |
| 3 | default | claude | 1 | 0 |
| 4 | cfgaware | claude | 1 | 0 |
| 5 | default | intent_gpt | 1 | 0 |
| 6 | cfgaware | intent_gpt | 1 | 0 |
| 7 | default | intent_claude | 1 | 0 |
| 8 | cfgaware | intent_claude | 1 | 0 |

Example (Claude Opus 4.5 on Amazon Bedrock):

    python experiments/rebuttal-20261007/run_generation.py \
        --provider bedrock --model-id us.anthropic.claude-opus-4-5-20251101-v1:0 \
        --label claude-opus-4-5 --max-tokens 16000 --workers 4 --cap 80 \
        --tasks experiments/benchmark-v2/tasks.jsonl --mode default --desc gpt --samples 5

`--dry-run` prints the first prompt without calling the model. The runner resumes: finished
(specification, sample) pairs are skipped, and a failed call is never saved, so running the same
command again retries it. Results go to `experiments/benchmark-v2/results/<label>__<mode>__<desc>desc/`
(`results.json` with one record per output and `generations/<id>_s<k>.tla`).
