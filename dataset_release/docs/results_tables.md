# TLA+ Spec-Generation Benchmark — Results

Denominators: gold (SANY+TLC) = **146**, silver (SANY-only) = **440**, full system = **586**, repos = **9**.

_Policy: pass@1 over full bucket denominator; missing/unparsed = fail; TLC on gold only; silver & intent are SANY-only._

All numbers are percentages. pass@1 is over the full bucket denominator (a spec that did not parse/extract counts as a failure).

## 1. Greedy baseline (1 sample/spec, declarative)

| Model | Gold SANY@1 | Gold TLC@1 | Silver SANY@1 | Full SANY@1 | Intent SANY@1 (gold) |
|---|---|---|---|---|---|
| qwen2.5-coder-32b | 24.0 | 1.4 | 23.0 | 23.2 | 21.2 |
| llama3.3-70b | 19.2 | 1.4 | 22.7 | 21.8 | 16.4 |
| gpt-oss-20b | 4.8 | 0.0 | 5.5 | 5.3 | 3.4 |
| deepseek-prover-v2-7b | 0.0 | 0.0 | 0.2 | 0.2 | 0.0 |
| llama3.2-3b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |
| mistral-7b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |

## 2. pass@1 / pass@5 / pass@10 (k=10 sampling, gold only)

Unbiased estimator; bootstrap 95% CI over specs in brackets.

| Model | Metric | pass@1 | pass@5 | pass@10 |
|---|---|---|---|---|
| qwen2.5-coder-32b | SANY | 21.4 [17.1, 25.9] | 49.2 [42.7, 55.6] | 64.4 [56.2, 71.9] |
| qwen2.5-coder-32b | TLC | 1.2 [0.0, 2.7] | 2.0 [0.0, 4.6] | 2.1 [0.0, 4.8] |
| gpt-oss-20b | SANY | 6.4 [5.1, 7.9] | 26.5 [21.6, 31.6] | 43.8 [36.3, 52.1] |
| gpt-oss-20b | TLC | 0.7 [0.3, 1.2] | 3.1 [1.2, 5.4] | 5.5 [2.1, 9.6] |
| llama3.3-70b | SANY | 17.0 [13.6, 20.6] | 43.2 [36.6, 50.2] | 56.2 [47.9, 64.4] |
| llama3.3-70b | TLC | 1.2 [0.0, 3.1] | 1.9 [0.0, 4.3] | 2.1 [0.0, 4.8] |

## 3a. SANY pass@1 by complexity tier (greedy)

| Model | basic (gold) | intermediate (gold) | advanced (gold) | basic (silver) | intermediate (silver) | advanced (silver) |
|---|---|---|---|---|---|---|
| qwen2.5-coder-32b | 42.0 | 21.6 | 6.7 | 33.5 | 22.1 | 10.2 |
| llama3.3-70b | 22.0 | 25.5 | 8.9 | 30.5 | 19.3 | 16.4 |
| gpt-oss-20b | 4.0 | 3.9 | 6.7 | 6.6 | 6.2 | 3.1 |
| deepseek-prover-v2-7b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.8 |
| llama3.2-3b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |
| mistral-7b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |

## 3b. Gold TLC pass@1 by complexity tier (greedy)

| Model | basic | intermediate | advanced |
|---|---|---|---|
| qwen2.5-coder-32b | 4.0 | 0.0 | 0.0 |
| llama3.3-70b | 4.0 | 0.0 | 0.0 |
| gpt-oss-20b | 0.0 | 0.0 | 0.0 |
| deepseek-prover-v2-7b | 0.0 | 0.0 | 0.0 |
| llama3.2-3b | 0.0 | 0.0 | 0.0 |
| mistral-7b | 0.0 | 0.0 | 0.0 |

## 3c. SANY pass@1 by source repository (greedy, full system)

| Model | Azure | TeamTilapia | apalache-mc | atomix | josehu07 | microsoft | pingcap | tendermint | tlaplus | micro | macro |
|---|---|---|---|---|---|---|---|---|---|---|---|
| qwen2.5-coder-32b | 0.0 | 50.0 | 28.2 | 16.7 | 19.4 | 0.0 | 9.1 | 23.5 | 22.5 | 23.2 | 18.8 |
| llama3.3-70b | 0.0 | 0.0 | 26.9 | 33.3 | 33.3 | 11.1 | 27.3 | 29.4 | 18.2 | 21.8 | 20.0 |
| gpt-oss-20b | 0.0 | 0.0 | 3.2 | 16.7 | 16.7 | 0.0 | 0.0 | 0.0 | 5.5 | 5.3 | 4.7 |
| deepseek-prover-v2-7b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.3 | 0.2 | 0.0 |
| llama3.2-3b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |
| mistral-7b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |

## 3d. Gold TLC pass@1 by source repository (greedy)

| Model | TeamTilapia | apalache-mc | josehu07 | microsoft | pingcap | tlaplus | micro | macro |
|---|---|---|---|---|---|---|---|---|
| qwen2.5-coder-32b | 0.0 | 9.1 | 0.0 | 0.0 | 0.0 | 0.8 | 1.4 | 1.6 |
| llama3.3-70b | 0.0 | 18.2 | 0.0 | 0.0 | 0.0 | 0.0 | 1.4 | 3.0 |
| gpt-oss-20b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |
| deepseek-prover-v2-7b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |
| llama3.2-3b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |
| mistral-7b | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 | 0.0 |

## 4. Outcome taxonomy (greedy declarative, gold denominator)

Mutually-exclusive fractions per model (sum to 100%).

| Model | extraction_failed | sany_fail | no_cfg | tlc_fail | tlc_pass |
|---|---|---|---|---|---|
| qwen2.5-coder-32b | 0.0 | 76.0 | 0.0 | 22.6 | 1.4 |
| llama3.3-70b | 0.0 | 80.8 | 0.0 | 17.8 | 1.4 |
| gpt-oss-20b | 0.7 | 94.5 | 0.0 | 4.8 | 0.0 |
| deepseek-prover-v2-7b | 11.0 | 89.0 | 0.0 | 0.0 | 0.0 |
| llama3.2-3b | 2.1 | 97.9 | 0.0 | 0.0 | 0.0 |
| mistral-7b | 42.5 | 57.5 | 0.0 | 0.0 | 0.0 |
