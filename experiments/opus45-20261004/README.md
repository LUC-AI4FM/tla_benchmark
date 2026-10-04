# Opus 4.5 supplementary runs (2026-10-04)

This release contains 700 experimental outputs over the benchmark's 100 evaluation
tasks, plus one separate smoke output. It preserves the historical release at
`90b1a31e7f2d3bb4901f9309ce0490ecef50ed8d` and its corrected 76/300 pooled
configuration-aware count.

All requests used Amazon Bedrock `us.anthropic.claude-opus-4-5-20251101-v1:0` in
`us-east-2`, `maxTokens=16000`, and provider-default temperature. No temperature was
included in the request. The recorded grader used Temurin 11.0.25+9, the pinned tools
jar, a 60-second SANY limit and a 300-second TLC limit.

## Results

| Run | Description | Prompt | Outputs | Archived SANY flag | `sany_semantic_ok` | Archived TLC pass |
|---|---|---|---:|---:|---:|---:|
| A1 | GPT declarative | Configuration-aware | 100 | 91 | 74 | 22 |
| A2 | Claude declarative | Default | 100 | 89 | 77 | 31 |
| A3 | GPT declarative | Default, samples 0–4 | 500 | 449 | 390 | 93 |
| Smoke | GPT declarative | Default, separate check | 1 | 1 | 0 | 0 |

A3 has five matched requests per task. Samples 1–4 are from the original delivery;
sample 0 is the fresh addendum with complete request, response and grading evidence.
Archived TLC passes for samples 0–4 are **19, 19, 19, 19, 17**. Matched author-protocol
**pass@5 is 27/100**: a task passes if any of its five samples passes. All 100 tasks
remain in the denominator. The original four-sample pass@4 remains **26/100**.

The historical released baseline has 16/100 passes, but lacks request-level model,
provider, token-limit and decoding provenance. Its union with the original four samples
is retained as mixed-baseline coverage, without treating it as a matched fifth sample.

`code/analysis/strict_sany.py` computes `sany_semantic_ok`: zero exit, completed semantic
processing, and no parse or semantic errors on either output stream. Harmless warnings
are allowed. The original delivery includes 75 author-true records with semantic errors,
including the separate smoke; fresh sample 0 adds 14. Original grades and raw logs are
preserved. The five original 300-second TLC timeouts remain nonpasses.

Compiler acceptance and author-protocol TLC passes do not establish faithfulness to the
natural-language description. A1 and A2 change both configuration exposure and description
source. Their difference does not isolate a description-provider effect. [report.json](report.json)
retains row-level outcomes, additional diagnostic qualifications and the 100/99/93-task
sensitivity strata; [tables.md](tables.md) is generated from those saved outputs.

## Frozen inputs

[inputs/manifest.jsonl](inputs/manifest.jsonl) is the exact manifest used to prepare these
requests, byte-identical to the original release. Its SHA256 is
`00e05ce51e157ded01e5a1a81040d77f6472bb0d05fec34e93f179294a6c31be`.
`protocol.json` pins this copy, the original specifications/configurations, grader,
validator and tools jar. Reproduction uses this snapshot even if the root manifest changes.

Verification rebuilds all **701 saved prompts**, including smoke, from
`desc_declarative_gpt` or `desc_declarative_claude` and the pinned prompt templates.
Configuration-aware prompts also use the original configuration-name extraction.
The reconstructed bytes must match both the saved prompt and its request payload/hash.
These runs did not use intent descriptions or the later split intent fields.

Each evidence directory retains the generated module, prompt, raw model text,
request/response, run metadata, original grade and raw checker logs. `provenance.json`
records the source hashes; `integrity.json` verifies the complete public file inventory.
Source modules, prompts, requests, responses and grades preserve their original bytes.
Checker logs retain diagnostics and return codes with workspace paths replaced by placeholders.

Frozen source archive SHA256 values:

- Original delivery: `6dcb2e5c2ddc39903c0a4c324a99bc80000bbb19bdb2f5c0a483ffa526651393`.
- Matched sample-0 addendum: `29179a1f5b2ea8af9a822ebb70d06e00f45087e9779ec648e2b3b588ddc85f96`.

## Reproduce

Python 3.10+ and its standard library verify the evidence and rebuild the report and
tables offline. Java is needed for the live compiler and saved-source regrading tests;
CI uses the recorded Temurin 11.0.25+9. No generation API or credentials are required.

```sh
python3 experiments/opus45-20261004/reproduce.py --check
python3 -m unittest discover -s experiments/opus45-20261004 -p 'test_*.py' -v
python3 -O -m unittest discover -s experiments/opus45-20261004 -p 'test_*.py' -v
python3 reproduce.py --clean
```

Tests exercise the full artifact/request/configuration joins, all five A3 sample slots,
strict compiler diagnostics, timeout evidence, hash tampering and changed upstream
manifests. Changing an output changes the derived counts. Changing a frozen description
breaks its saved-prompt match.

For an optional local regrade, select the recorded JDK and write a new result outside
this evidence directory:

```sh
python3 experiments/opus45-20261004/regrade.py --run-id A1:1343:s0 \
  --java /path/to/temurin-11.0.25+9/bin/java --output /tmp/opus45-regrade.json
```

The separate experimental reference audit and its completed checker evidence are preserved
on [wip/reference-audit](https://github.com/LUC-AI4FM/tla_benchmark/tree/wip/reference-audit/experiments/opus45-20261004).
Specification licensing follows the source repositories in the frozen manifest;
description and annotation licensing follows the root `LICENSE`.
