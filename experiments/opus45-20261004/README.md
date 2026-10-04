# Opus 4.5 supplementary evidence (2026-10-04)

This additive release contains 700 experimental outputs and one separate smoke output.
It preserves the historical release at `90b1a31e7f2d3bb4901f9309ce0490ecef50ed8d`, including
its corrected 76/300 configuration-aware pooled count. Original scores and raw sources
remain intact; additional qualifications and reference checks have their own fields.

Requests use Amazon Bedrock `us.anthropic.claude-opus-4-5-20251101-v1:0` in `us-east-2`,
`maxTokens=16000`, and provider-default temperature (omitted from the request).
Original prompts, references, configurations, grader and tools jar are unchanged.

## Derived results and score definitions

[Generated tables](tables.md) are rendered by `reproduce.py` from the saved outputs;
`--check` verifies both `report.json` and the Markdown tables. The A3 cohort now contains
five fresh matched samples per task: samples 1-4 from the original delivery and an additive
sample 0 with complete request/response/grading provenance. Archived TLC passes per
sample 0-4 are **19, 19, 19, 19, 17**. Empirical archived-protocol pass@5 is **27/100**;
with n=k=5, each task scores one if any recorded sample passes and zero otherwise.
All 100 tasks, including failures, remain in the mean. Independence and an uncertainty
interval are not asserted.

`qualified_checked_tlc_pass` additionally requires `sany_semantic_ok`, a resolved original
configuration, enabled named invariants/properties, evidence of nonempty initial states,
completed checking, exit code zero and no error diagnostics. Its matched any-pass@5 is
**18/100**. This qualification still does not certify natural-language faithfulness.
Every output has original and recomputed outcomes, configuration source, named checks,
and row-level reasons in `report.json`.

The primary denominator remains the full 100 IDs. Sensitivity tables separately retain
99 tasks with original configurations and 93 after also excluding six documented
single-state reference fixtures. Missing-configuration item 1142 cannot count as a pass.
A successful unchecked model run cannot satisfy the named-check qualification.

The original four-sample result remains **26/100**. The historical released baseline
still has 16/100 passes and lacks request-level generation settings. Its descriptive
union with the original four samples remains 27/100, explicitly uncertified as pass@5.
The matched five-sample result uses the newly generated sample 0, never that baseline.

## Compiler correction

SANY can exit zero while reporting semantic errors. `code/analysis/strict_sany.py` adds
an opt-in diagnostic-aware compiler result, named **`sany_semantic_ok`** here: zero exit,
completed semantic processing, and no parse/semantic errors on either stream. Harmless
warnings do not fail this check. This is a compiler result, not an adequacy metric.

The original delivery has 75 author-true semantic-error records: 17 A1, 12 A2, 45 A3,
and one separate smoke. The fresh sample 0 adds 14, making 59 across the matched
500-output A3 cohort. All original flags and diagnostics are retained, with separate
recomputed results. The five original 300-second TLC timeouts remain nonpasses;
two belong to A3. The fresh sample 0 has no such timeout.

## Independent reference checks and evaluator controls

`semantic_audit.py` implements checks for experimentally passing outputs against a separate,
frozen reference module through TLA+ `INSTANCE`, with explicit identity substitutions.
The reference and original configuration predate these outputs. The audit first checks
the reference itself, then checks reference-owned configured properties, whether the
reference allows the generated behaviors, and whether the generated specification
allows reference behaviors. The reverse direction exposes omitted behavior that a
safety-only check would miss. Candidate-owned tautologies cannot weaken the external
reference properties.

This is **post-generation validation of frozen reference contracts**. It is not a
preregistered natural-language assessment. Only identical, resolvable variable/constant
interfaces receive automatic bindings. Renamed variables, incompatible representations,
ambiguous dependencies and unsupported behavior contracts are reported as unresolved;
no inferred mapping or human judgment is invented. Original reference configurations
and derived audit configurations are labeled separately. Derived configurations preserve
the original constants/constraints while replacing the checks with external aliases.

The local audit uses the recorded Temurin 11.0.25+9 runtime and pinned jar, a bounded 512-MiB JVM heap, one TLC worker,
seed 1, fingerprint 0, a 60-second compiler limit and **5 seconds per independent TLC
check**. This bounded audit's timeouts are unresolved outcomes, distinct from the original
300-second experimental timeouts. Neither parser/configuration failures nor timeouts are
semantic counterexamples. Checking executions are reused only when task ID, generated
module hash, reference hash and original configuration hash are identical. Every condition
and sample retains its own output row and the execution origin is recorded explicitly.

`semantic-evidence.json` retains full checker logs, exact derived configurations, source
hashes, substitutions, and outcomes. `reduce_semantics.py` reconstructs every wrapper,
verifies its modules/configuration/mapping and derives `semantic-report.json` from raw
logs. External qualification requires the original named-check qualification plus a
nonempty completed reference control and success in all three external checks. It remains
a bounded reference result, not a certificate that the description faithfully expresses
all intended requirements. Unresolved and counterexample components remain visible.

The target includes all **700 experimental outputs**, including the fresh A3 sample 0;
the separate smoke output is excluded. The original delivery supplies 127 passing rows
with 114 unique input keys. Fresh sample 0 adds 19 passing rows: 13 new input keys and
6 identical inputs that reuse existing executions. The final target is therefore
**146 passing rows and 127 unique input keys** across A1/A2/A3 and all five A3 samples.
`semantic-report.json` derives this inventory from the frozen outputs and records each
row's condition, sample and full execution input key.

The saved checkpoint is **incomplete: 44 of 146 passing outputs audited, 42 of 127
unique input keys**. All 18 previously published records remain unchanged. The continuation
stopped when the coordination host's configured local compute policy terminated the
checker workload. No checker was active at checkpoint publication; 85 unique checks
remain. `semantic-report.json` lists every unexecuted run explicitly.
The default reducer rejects incomplete evidence; `--allow-partial` verifies the checkpoint
without certifying a population score. The archived matched pass@5 and named-check
qualification above have complete evidence coverage independently of this partial audit.
Audit continuation accepts the same evaluator, runtime, settings and unchanged sources:
use `--resume --max-new-outputs 1` to checkpoint bounded batches.

`continue_reference_audit.py` additionally supports an explicitly qualified execution
profile for the authorized NUC continuation. It retains the frozen evaluator and checker
hashes and the same 60-second SANY/5-second TLC limits, 512-MiB heap, one worker,
seed and fingerprint. Installed Temurin 25.0.3+9-LTS receives its own actual Linux
runtime receipt after the retained evaluator controls pass; it is never labeled Java 11.
This qualification covers those finite controls, not exhaustive JVM equivalence.
Original records remain unchanged, completed generated-source groups are skipped, and
existing reference controls are reused with explicit source/profile pointers. Checkpoints
are written atomically outside the integrity-protected inputs. The legacy `runtime` field
describes the original Mac profile; additional receipts and per-row profile IDs describe
subsequent executions. Human faithfulness assessment remains separate and unreviewed.

Live regression fixtures establish that replacing a valid invariant by TRUE or removing
its check preserves the already passing state graph, while FALSE is rejected on a model
whose control establishes nonempty Init. A known broken transition is rejected by a
frozen external invariant even when the candidate substitutes TRUE. A disabled transition
passes forward inclusion but fails reverse inclusion. Actual zero-exit semantic-error
logs, harmless warnings, malformed evidence, compiler/configuration errors, incomplete
checking and timeouts exercise the fail-closed paths. Errors and timeouts never count
as semantic mutation kills.

## Description comparison and remaining human review

A1 changes both configuration exposure and description source relative to A2. Their
22 versus 31 archived passes do not isolate a description-provider effect.
`paired_default_description_comparison` instead joins A2 with default/GPT-description
A3 on the same 100 tasks, comparing A2's one sample to the original four A3 samples'
mean pass rate. It includes task-level paired differences and source-repository sensitivity.
This is descriptive: unequal draw counts and unresolved description equivalence limit
causal interpretation.

`description-review-cases.jsonl` supplies 100 independent-human review cases with a
common frozen reference/configuration contract and two descriptions. The packet omits
candidate outputs and provider/model labels; all assessments are explicitly **unreviewed**.
A reviewer should compare both descriptions against the reference's allowed and required
behavior, record missing/added requirements and ambiguity, and judge equivalence before
consulting labeled generations. The original repository contains labeled descriptions,
so reviewers need to use the packet first to preserve that blinding. Renamed-interface
or unresolved semantic cases also require explicit reviewed mappings or a documented
reason they cannot be compared. No agent result is presented as human agreement.

To rebuild the packet and keep its assignment key outside the publication:

```sh
python3 experiments/opus45-20261004/build_review_cases.py \
  --output /tmp/description-review-cases.jsonl --private-key /tmp/description-review-key.json
```

## Reproduce offline

Python 3.10+ and its standard library suffice for verification, reductions and tables.
Java is used only for live compiler/checker controls; set `TLA_TEST_JAVA` to select a JDK.
CI uses the recorded Temurin 11.0.25+9. No generation API, credentials or Python packages
are required.

```sh
python3 experiments/opus45-20261004/reproduce.py --check
python3 experiments/opus45-20261004/reduce_semantics.py --allow-partial --check
python3 -m unittest discover -s experiments/opus45-20261004 -p 'test_*.py' -v
python3 -O -m unittest discover -s experiments/opus45-20261004 -p 'test_*.py' -v
python3 reproduce.py --clean
```

Tests verify complete artifact/request/config joins and sample coverage, mutate inputs to
prove counts depend on outputs, and reject missing/duplicate rows, mismatched models,
hash tampering, empty output, incomplete checker evidence and invented classifications.
They also execute a saved generated source through the original grading workflow.
For additional local checks, write results outside the frozen evidence directory:

```sh
python3 experiments/opus45-20261004/regrade.py \
  --run-id A1:1343:s0 --java /path/to/temurin-11.0.25+9/bin/java \
  --output /tmp/opus45-1343-regrade.json
python3 experiments/opus45-20261004/semantic_audit.py \
  --java /path/to/temurin-11.0.25+9/bin/java --workers 1 --timeout 5 \
  --output /tmp/opus45-independent-audit.json
python3 experiments/opus45-20261004/reduce_semantics.py \
  --evidence /tmp/opus45-independent-audit.json --json
```

Reruns preserve archived results. Stochastic reference item 875 can yield a different local
verdict; neither rerun outcomes nor unsupported cases filter the primary denominators.

## Integrity and publication scope

Each evidence directory contains the exact generated module, prompt, raw model text,
request/response, planned run and author grade, plus raw checker evidence and public
run metadata. `protocol.json` pins all 1,746 original specification/configuration files
and the grader, validator, manifest and tools jar. `provenance.json` binds all 701 source
chains to their frozen source hashes. `integrity.json` verifies all public artifacts and
required repository inputs. Canonical protocol hashes use sorted compact JSON; file
hashes use the exact original bytes.

Generated sources, prompts, requests, responses and grades remain byte-identical to their
source. Checker messages and return codes are preserved, with absolute workspace paths
replaced by `<WORKSPACE>` or `<AUDIT_TMP>` and JSON serialized consistently. Private
operational, billing, access and identity records are excluded. Original source archives
remain unchanged. There were 706 source API attempts: 701 retained outputs, including
smoke, and five original access failures that produced no output.

Frozen archive SHA256 values:

- Original delivery: `6dcb2e5c2ddc39903c0a4c324a99bc80000bbb19bdb2f5c0a483ffa526651393`.
- Matched fifth-sample addendum: `29179a1f5b2ea8af9a822ebb70d06e00f45087e9779ec648e2b3b588ddc85f96`.

Specification licensing follows source repositories in `manifest.jsonl`;
description/annotation licensing follows the root `LICENSE`. Paper files are unchanged.
