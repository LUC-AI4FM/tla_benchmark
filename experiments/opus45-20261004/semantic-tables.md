# Independent bounded reference audit

Coverage: 146/146 passing output rows; 127/127 unique input keys.

| Condition | Passing rows audited | External reference-qualified outputs | Counterexample outputs | Outputs with unresolved components |
|---|---:|---:|---:|---:|
| A1 | 22/22 | 2 | 7 | 17 |
| A2 | 31/31 | 10 | 5 | 18 |
| A3 | 93/93 | 31 | 11 | 54 |

Counterexample and unresolved columns can overlap when different components have different outcomes.
External qualification requires the original named-check/nonempty qualification and all four reference components to hold.

| A3 task stratum | External reference-qualified any-pass across samples 0–4 |
|---|---:|
| full_primary | 7/100 |
| with_original_configuration | 7/99 |
| without_missing_cfg_or_single_state_fixtures | 5/93 |

| Execution profile | Output rows |
|---|---:|
| Linux / Temurin 25.0.3+9-LTS | 102 |
| Original Mac / Temurin 11.0.25+9 | 44 |

Reference controls retain their separately recorded execution source/profile when reused.
These are bounded results under mixed execution profiles, not natural-language faithfulness certification.
All 100 description-equivalence cases remain unreviewed.
