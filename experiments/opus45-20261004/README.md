# Opus 4.5 supplementary runs (2026-10-04)

This additive release contains 600 new experimental outputs plus one separate smoke output.
It preserves the historical release at `90b1a31e7f2d3bb4901f9309ce0490ecef50ed8d` and its
corrected 76/300 configuration-aware pooled count. It does not replace historical scores.

The requests use Amazon Bedrock `us.anthropic.claude-opus-4-5-20251101-v1:0` in `us-east-2`,
`maxTokens=16000`, and provider-default temperature (the parameter is omitted).
The prompt protocol and original reference configurations are unchanged.

| Experiment | Description source | Mode | Outputs | Archived SANY flag | Strict SANY | TLC passes |
|---|---|---|---:|---:|---:|---:|
| A1 | GPT declarative | Configuration-aware | 100 | 91 | 74 | 22 |
| A2 | Claude declarative | Default | 100 | 89 | 77 | 31 |
| A3 | GPT declarative | Default, samples 1-4 | 400 | 360 | 315 | 74 |
| Smoke (separate) | GPT declarative | Default | 1 | 1 | 0 | 0 |

Every table value is computed from the saved evidence by `reproduce.py`; `report.json` is its
derived machine-readable result. A3 TLC passes per sample are 19, 19, 19, and 17.
The full 100-ID denominator includes missing-configuration item 1142 and the six single-state
fixtures identified in the historical release. A TLC pass means success under the supplied
configuration; it does not establish equivalence to the reference or natural-language intent.

## Reproduce offline

Python 3.10+ and its standard library suffice for evidence verification and table reductions.
From the repository root:

```sh
python3 experiments/opus45-20261004/reproduce.py --check
python3 experiments/opus45-20261004/reproduce.py --check --json
python3 -m unittest discover -s experiments/opus45-20261004 -p 'test_*.py' -v
python3 -O -m unittest discover -s experiments/opus45-20261004 -p 'test_*.py' -v
python3 reproduce.py --clean
```

The tests execute the complete 601-output verification/reduction, independently reduce
archived grades, mutate an output to prove counts respond to data, and reject missing records,
hash tampering, extra files, and request/model mismatches. A small real SANY fixture checks its
zero-exit semantic-error behavior when Java is available; set `TLA_TEST_JAVA` to select a JDK.
No generation API, credentials, or Python packages are required.

For a new local SANY/TLC execution of a recorded output, provide the original runtime:

```sh
python3 experiments/opus45-20261004/regrade.py \
  --run-id A1:1343:s0 --java /path/to/temurin-11.0.25+9/bin/java \
  --output /tmp/opus45-1343-regrade.json
```

This command uses the unchanged release grader, module/dependency staging, jar, and reference
configuration; SANY has a 60-second limit and TLC a 300-second limit. It writes a new result
outside the immutable evidence directory. The five archived 300-second TLC timeouts remain
nonpasses. Item 875 is stochastic, so a new local verdict need not equal the archived verdict.
Local reruns do not replace or filter the recorded results.

## Strict parser correction

The archived author grader used SANY's exit code alone. SANY can return zero while reporting
semantic errors. Seventy-five author-true records contain such errors: 17 A1, 12 A2, 45 A3,
and one smoke. `code/analysis/strict_sany.py` adds an opt-in diagnostic-aware interpretation:
exit code zero, completed semantic processing, and no parse/semantic-error diagnostics on
either stream. `report.json` lists every affected run. Original flags, diagnostics, and TLC
scores remain available; strict SANY is a separately labeled derived result, not a new run.

## Four-sample coverage and the baseline limit

The four matched A3 samples give empirical TLC pass@4 of **26/100 (26%)**: with n=k=4,
each specification scores one if any recorded sample passes, otherwise zero. All 100 remain
in the mean. No sampling independence or uncertainty interval is asserted.

The released Opus baseline has 16/100 TLC passes; 15 overlap A3's any-pass set. Combining
that baseline with the four new samples gives **27/100 descriptive mixed coverage**.
Only item 1595 increases the union. This is **not certified strict pass@5**.

| Baseline vs new A3 | Compatibility evidence |
|---|---|
| Evaluation IDs and denominator | Same ordered 100 IDs, including all failures/fixtures |
| Descriptions and prompts | Manifest and prompt templates identical; new requests match the templates; historical request prompts unrecorded |
| Specifications/configurations | All 1,746 released `.tla`/`.cfg` inputs byte-identical; 99 evaluation configurations, item 1142 absent in both |
| Grader, validator, tools jar | Byte-identical, hashes in `protocol.json` |
| Model identity and generation settings | New requests have exact Bedrock model ID, provider, token budget and omitted temperature; baseline has only a display label |
| Runtime/seed control | Historical Linux/JDK 11 vs new macOS/Temurin 11.0.25+9; seeds not controlled |

The archived baseline lacks request-level snapshot/provider, prompt receipts, output-token
budget, decoding settings, and sample provenance. Compatible content cannot certify an
additional matched draw. No fifth sample was generated or substituted.

## Artifact integrity and publication scope

Each `evidence/<job>/<id>_s<sample>/` directory contains the exact generated TLA module,
prompt, raw model text, request/response payload, planned run, archived author grade, and
raw checker evidence. `metadata.json` records public scientific provenance. `protocol.json`
pins all original specification/configuration dependencies and the exact grader/jar.
`provenance.json` links public artifacts and source chains to the frozen input digests;
`integrity.json` verifies every public file and required repository input.

Generated modules, prompts, requests, responses, and author grades are byte-identical to the
audited source. Checker diagnostics retain every message and return code, with absolute
workspace paths replaced by `<WORKSPACE>` and JSON serialized consistently. The original
private archives are unchanged. Operational access/billing/identity records, task logs,
credentials, and duplicate packages are excluded. Of 606 source API attempts, 601 produced
the retained outputs; five failed access attempts produced no output and do not inflate the
scientific denominators. Source archive SHA256:
`6dcb2e5c2ddc39903c0a4c324a99bc80000bbb19bdb2f5c0a483ffa526651393`.

Specification licensing follows the original source repositories recorded in `manifest.jsonl`;
description/annotation licensing follows the root `LICENSE`. The historical release and
paper files are unchanged.
