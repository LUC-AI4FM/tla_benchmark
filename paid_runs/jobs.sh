#!/usr/bin/env bash
# Generation runs for TLA+-Bench. Run from anywhere, e.g. ./paid_runs/jobs.sh I1
# Each job resumes if interrupted: re-run the same line to continue.
# Every job writes to paid_runs/results/<label>__<mode>__<desc>desc/ ; commit those folders.
set -euo pipefail
cd "$(dirname "$0")"

# Bedrock inference-profile id for Claude Opus 4.5. Confirm it in the Bedrock console
# (Model catalog -> Claude Opus 4.5 -> inference profile) and change it here if it differs.
OPUS_ID="${OPUS_ID:-us.anthropic.claude-opus-4-5-20251101-v1:0}"

case "${1:-help}" in

# ---------------------------------------------------------------- AWS Bedrock (Claude Opus 4.5)
smoke)   # 1 specification, about $0.10: checks credentials, model access and grading
  python run_generation.py --provider bedrock --model-id "$OPUS_ID" --label smoke-opus \
    --mode default --desc gpt --max-tokens 16000 --limit 1 --workers 1 ;;

A1)      # configuration-aware regime, all 100, same 16,000-token budget as the other models
  python run_generation.py --provider bedrock --model-id "$OPUS_ID" --label claude-opus-4-5 \
    --mode cfgaware --desc gpt --max-tokens 16000 --workers 4 --cap 30 ;;

A2)      # cross-provider: default regime on the Claude-written descriptions
  python run_generation.py --provider bedrock --model-id "$OPUS_ID" --label claude-opus-4-5 \
    --mode default --desc claude --max-tokens 16000 --workers 4 --cap 30 ;;

A3)      # repeated samples: 4 more default-regime samples at the main run's settings
         # (sample 0 is the released run, so these are samples 1-4)
  python run_generation.py --provider bedrock --model-id "$OPUS_ID" --label claude-opus-4-5 \
    --mode default --desc gpt --samples 4 --sample-offset 1 --max-tokens 16000 --workers 4 --cap 80 ;;

# ---------------------------------------------------------------- OpenAI (GPT-5), needs OPENAI_API_KEY
B1)      # cross-provider; the free tier allows 50 requests a day, so this stops and resumes
  python run_generation.py --provider openai --model-id gpt-5-2025-08-07 --label gpt-5 \
    --mode default --desc claude --max-tokens 16000 --workers 1 --min-interval 30 --cap 15 ;;

B2)      # repeated samples 1-4 (sample 0 is the released run)
  python run_generation.py --provider openai --model-id gpt-5-2025-08-07 --label gpt-5 \
    --mode default --desc gpt --samples 4 --sample-offset 1 --max-tokens 16000 \
    --workers 1 --min-interval 30 --cap 30 ;;

# ---------------------------------------------------------------- Google (Gemini 2.5 Pro), needs GEMINI_API_KEY
C1)      # cross-provider, same decoding as the released default run (temperature 0, default length)
  python run_generation.py --provider google --model-id gemini-2.5-pro --label gemini-2-5-pro \
    --mode default --desc claude --temperature 0 --max-tokens 0 --workers 4 --cap 15 ;;

C2)      # repeated samples at the provider-default temperature (temperature 0 would repeat itself)
  python run_generation.py --provider google --model-id gemini-2.5-pro --label gemini-2-5-pro-default-temp \
    --mode default --desc gpt --samples 5 --max-tokens 0 --workers 4 --cap 50 ;;

# ---------------------------------------------------------------- open models (any GPU machine with Ollama)
D)       # cross-provider for the open models, with their own prompt template and settings
  for m in qwen2.5-coder:32b llama3.3:70b gpt-oss:20b; do
    python run_generation.py --provider ollama --model-id "$m" --label "${m//:/-}" \
      --mode default --desc claude --template open --temperature 0 --max-tokens 8192 \
      --num-ctx 12288 --workers 1 --cap 0.01
  done ;;

# ---------------------------------------------------------------- intent (name-hidden) descriptions
# Each job runs both intent sets (intent_gpt pairs with the main GPT-written results) in both
# regimes: default (no names given) and configuration-aware (the configuration's names given),
# with the settings of the paper's runs in that regime.
I1)      # Claude Opus 4.5 on Bedrock (as A2/A3 and A1)
  for mode in default cfgaware; do for d in intent_gpt intent_claude; do
    python run_generation.py --provider bedrock --model-id "$OPUS_ID" --label claude-opus-4-5 \
      --mode $mode --desc $d --max-tokens 16000 --workers 4 --cap 30
  done; done ;;

I2)      # GPT-5 (needs OPENAI_API_KEY); on a free-tier key use --workers 1 --min-interval 30
  for mode in default cfgaware; do for d in intent_gpt intent_claude; do
    python run_generation.py --provider openai --model-id gpt-5-2025-08-07 --label gpt-5 \
      --mode $mode --desc $d --max-tokens 16000 --workers 4 --cap 30
  done; done ;;

I3)      # Gemini 2.5 Pro (needs GEMINI_API_KEY): temperature 0; default length in the default
         # regime and 16,000 tokens in the configuration-aware regime, as in the paper's runs
  for d in intent_gpt intent_claude; do
    python run_generation.py --provider google --model-id gemini-2.5-pro --label gemini-2-5-pro \
      --mode default --desc $d --temperature 0 --max-tokens 0 --workers 4 --cap 15
    python run_generation.py --provider google --model-id gemini-2.5-pro --label gemini-2-5-pro \
      --mode cfgaware --desc $d --temperature 0 --max-tokens 16000 --workers 4 --cap 15
  done ;;

I4)      # open models (any GPU machine with Ollama), same settings as job D
  for mode in default cfgaware; do for d in intent_gpt intent_claude; do
    for m in qwen2.5-coder:32b llama3.3:70b gpt-oss:20b; do
      python run_generation.py --provider ollama --model-id "$m" --label "${m//:/-}" \
        --mode $mode --desc $d --template open --temperature 0 --max-tokens 8192 \
        --num-ctx 12288 --workers 1 --cap 0.01
    done
  done; done ;;

D0)      # open models on the GPT-written declarative descriptions, graded with the same strict
         # rule as every other run (the paper's June runs repaired a missing module header)
  for m in qwen2.5-coder:32b llama3.3:70b gpt-oss:20b; do
    python run_generation.py --provider ollama --model-id "$m" --label "${m//:/-}" \
      --mode default --desc gpt --template open --temperature 0 --max-tokens 8192 \
      --num-ctx 12288 --workers 1 --cap 0.01
  done ;;

check)   # summary of everything in results/
  python check_results.py ;;

*) echo "usage: ./jobs.sh {smoke|A1|A2|A3|B1|B2|C1|C2|D|D0|I1|I2|I3|I4|check}" ;;
esac
