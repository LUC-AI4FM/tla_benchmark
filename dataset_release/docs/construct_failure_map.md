# Construct-Level Failure Map — TLA+ Spec Generation Benchmark

Declarative greedy baseline (pass@1, `gpt` descriptions). System-core specs only (gold_system + silver_system). SANY denominators are **all** system specs, not conditional on parsing. TLC pass rates are computed on the **gold** subset, where a spec passes only if `tlc_status=="ran"` and `tlc_pass` is true (absence = fail).

Models pooled: deepseek-prover-v2-7b, gpt-oss-20b, llama3.2-3b, llama3.3-70b, mistral-7b, qwen2.5-coder-32b
Strong models: qwen2.5-coder-32b, llama3.3-70b
Specs with missing/unparseable feature files (excluded from construct splits): 0

## Overall pass rates

| Metric | Pooled (all models) | Strong models |
|---|---|---|
| SANY pass@1 | 8.4% (296/3516) | 22.5% (264/1172) |
| TLC pass@1 (gold) | 0.5% (4/876) | 1.4% (4/292) |

## Per-model overall

| Model | SANY pass@1 | TLC pass@1 (gold) |
|---|---|---|
| deepseek-prover-v2-7b | 0.2% (1/586) | 0.0% (0/146) |
| gpt-oss-20b | 5.3% (31/586) | 0.0% (0/146) |
| llama3.2-3b | 0.0% (0/586) | 0.0% (0/146) |
| llama3.3-70b | 21.8% (128/586) | 1.4% (2/146) |
| mistral-7b | 0.0% (0/586) | 0.0% (0/146) |
| qwen2.5-coder-32b | 23.2% (136/586) | 1.4% (2/146) |

## SANY pass rate by construct

Sorted by gap (most negative = construct most depresses pass rate).

### Pooled (all models)

| Construct | WITH rate (n) | WITHOUT rate (n) | Gap (with − without) |
|---|---|---|---|
| has_quantifiers | 6.9% (168/2442) | 11.9% (128/1074) | -5.0 pp |
| has_fairness | 5.3% (63/1182) | 10.0% (233/2334) | -4.7 pp |
| has_choice | 5.2% (33/636) | 9.1% (263/2880) | -3.9 pp |
| has_temporal | 7.7% (198/2562) | 10.3% (98/954) | -2.5 pp |
| has_liveness | 7.7% (197/2544) | 10.2% (99/972) | -2.4 pp |
| has_proofs | 6.4% (18/282) | 8.6% (278/3234) | -2.2 pp |
| has_pluscal | 6.6% (45/678) | 8.8% (251/2838) | -2.2 pp |
| safety_only | 10.3% (98/954) | 7.7% (198/2562) | +2.5 pp |

### Strong models (qwen2.5-coder-32b + llama3.3-70b)

| Construct | WITH rate (n) | WITHOUT rate (n) | Gap (with − without) |
|---|---|---|---|
| has_quantifiers | 18.2% (148/814) | 32.4% (116/358) | -14.2 pp |
| has_fairness | 14.2% (56/394) | 26.7% (208/778) | -12.5 pp |
| has_choice | 14.2% (30/212) | 24.4% (234/960) | -10.2 pp |
| has_temporal | 20.1% (172/854) | 28.9% (92/318) | -8.8 pp |
| has_liveness | 20.2% (171/848) | 28.7% (93/324) | -8.5 pp |
| has_pluscal | 16.4% (37/226) | 24.0% (227/946) | -7.6 pp |
| has_proofs | 17.0% (16/94) | 23.0% (248/1078) | -6.0 pp |
| safety_only | 28.9% (92/318) | 20.1% (172/854) | +8.8 pp |

## TLC pass rate by construct (gold subset)

### Pooled (all models)

| Construct | WITH rate (n) | WITHOUT rate (n) | Gap (with − without) |
|---|---|---|---|
| has_liveness | 0.1% (1/768) | 2.8% (3/108) | -2.6 pp |
| has_temporal | 0.1% (1/768) | 2.8% (3/108) | -2.6 pp |
| has_quantifiers | 0.0% (0/576) | 1.3% (4/300) | -1.3 pp |
| has_fairness | 0.0% (0/396) | 0.8% (4/480) | -0.8 pp |
| has_pluscal | 0.0% (0/180) | 0.6% (4/696) | -0.6 pp |
| has_choice | 0.0% (0/162) | 0.6% (4/714) | -0.6 pp |
| has_proofs | 0.0% (0/72) | 0.5% (4/804) | -0.5 pp |
| safety_only | 2.8% (3/108) | 0.1% (1/768) | +2.6 pp |

### Strong models

| Construct | WITH rate (n) | WITHOUT rate (n) | Gap (with − without) |
|---|---|---|---|
| has_liveness | 0.4% (1/256) | 8.3% (3/36) | -7.9 pp |
| has_temporal | 0.4% (1/256) | 8.3% (3/36) | -7.9 pp |
| has_quantifiers | 0.0% (0/192) | 4.0% (4/100) | -4.0 pp |
| has_fairness | 0.0% (0/132) | 2.5% (4/160) | -2.5 pp |
| has_pluscal | 0.0% (0/60) | 1.7% (4/232) | -1.7 pp |
| has_choice | 0.0% (0/54) | 1.7% (4/238) | -1.7 pp |
| has_proofs | 0.0% (0/24) | 1.5% (4/268) | -1.5 pp |
| safety_only | 8.3% (3/36) | 0.4% (1/256) | +7.9 pp |

## SANY pass rate by complexity tier

| Tier | Pooled (all models) | Strong models |
|---|---|---|
| basic | 11.7% (152/1302) | 32.0% (139/434) |
| intermediate | 8.1% (95/1176) | 21.4% (84/392) |
| advanced | 4.7% (49/1038) | 11.8% (41/346) |

## Construct prevalence (unique system specs)

| Construct | Specs with | Fraction |
|---|---|---|
| has_liveness | 424/586 | 72.4% |
| has_fairness | 197/586 | 33.6% |
| has_pluscal | 113/586 | 19.3% |
| has_proofs | 47/586 | 8.0% |
| has_temporal | 427/586 | 72.9% |
| has_quantifiers | 407/586 | 69.5% |
| has_choice | 106/586 | 18.1% |
| safety_only | 159/586 | 27.1% |
