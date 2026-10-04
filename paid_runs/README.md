# Generation runs for the rebuttal and the full version

This folder runs language models on the 100 evaluation specifications and grades every output
with SANY and TLC. It uses the specifications, manifest, descriptions, grader and TLC jar from
the repository root, so nothing is duplicated here. No API keys are included or needed in the
repository.

## Setup

1. **Java 11 or newer** for TLC: `java -version`.
2. **Python 3.10 or newer**: `pip install -r paid_runs/requirements.txt`
3. **AWS credentials** with Bedrock access (`aws configure`, `AWS_PROFILE` or an instance role).
   Set `AWS_REGION` if it is not `us-east-1`. The scripts use the inference profile
   `us.anthropic.claude-opus-4-5-20251101-v1:0`; if yours differs, `export OPUS_ID=<id>`.

All commands run from the repository root, for example `./paid_runs/jobs.sh I1`.

## Jobs

| Job | Model | What it answers | Requests | Status |
|---|---|---|---|---|
| A1 | Claude Opus 4.5 | Configuration-aware regime at 16,000 tokens | 100 | done (PR #39) |
| A2 | Claude Opus 4.5 | Claude-written declarative descriptions | 100 | done (PR #39) |
| A3 | Claude Opus 4.5 | 4 more samples on the GPT-written descriptions | 400 | done (PR #39) |
| **I1** | Claude Opus 4.5 | **Both intent (name-hidden) description sets, in both regimes** | 400 | **to run** |
| B1, I2 | GPT-5 | Claude-written and intent descriptions | | run by the authors |
| C1, I3 | Gemini 2.5 Pro | Claude-written and intent descriptions | | run by the authors |
| D, D0, I4 | open models | Claude-written, GPT-written (strict grading) and intent descriptions | | run by the authors |

I1 runs both intent sets (`descriptions/intent_gpt/`, `descriptions/intent_claude/`) in the
default regime (no names given) and in the configuration-aware regime (the names the
reference configuration checks are listed in the prompt). The intent text hides the module's
names, while TLC checks operators by name, so the second regime separates understanding the
system from guessing its names. Settings: 16,000 output tokens and provider-default
temperature, as in A1 to A3. Rough cost: $30 to $60.

Every job can be stopped and restarted with the same command; finished items are skipped.
A job stops by itself if its estimated spend passes the cap in `jobs.sh`. Failed requests are
not saved and are retried on the next run. `./paid_runs/jobs.sh check` prints, per result
folder, how many items are graded and the correct count per sample.

## Results

Each job writes `paid_runs/results/<model>__<mode>__<description>desc/`, holding
`results.json` (one graded record per item and sample) and the generated `.tla` files.
Commit these folders to this branch. Specification 875 draws a random graph on each TLC run,
so its verdict can differ between runs.
