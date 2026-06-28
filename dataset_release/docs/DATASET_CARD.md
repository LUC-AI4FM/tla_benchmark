# TLA+ Spec-Generation Benchmark — Dataset Card

**What it is.** An execution-grounded benchmark of real-world TLA+ specifications, each one
machine-verified, for evaluating LLM spec generation. Grading is the model checker's verdict
(SANY parse + TLC model-check), never text similarity.

## Provenance & construction (all reproducible)
- **Raw corpus:** 1,614 `.tla` modules harvested from public GitHub TLA+ repositories
  (tlaplus, apalache-mc, josehu07, pingcap, microsoft, Azure, atomix, tendermint, TeamTilapia).
- **Verification tool:** `tla2tools.jar` (SANY + TLC). Decision rule: SANY parse → valid-cfg
  check (all refs in reachable closure, all CONSTANTS assigned) → TLC verdict.
- **Cleaning funnel (213 dropped, audited):** 88 SANY-invalid, 68 tooling/negative-test
  counterexamples, 42 test fixtures, 15 runtime-error modules. Test fixtures and
  intentionally-broken tooling files were pruned so they can't be mistaken for real specs.
- **Classification:** every spec tagged system-vs-utility by a **3-model vote**
  (llama3.3:70b, qwen2.5-coder:32b, gpt-oss:120b); 91% unanimous on gold, contested cases
  flagged for human review.

## Final dataset (lives in `data/dataset_manifest/` + source modules in `data/tla_files/`)

| Bucket | Grading | Count | System / Utility |
|---|---|---|---|
| **gold** | SANY + TLC (model-checked) | **403** | 146 / 257 |
| **silver** | SANY only (no runnable cfg) | **897** | 440 / 457 |
| counterexample (preserved) | TLC failing traces | 14 | — |

- **Gold source repos:** tlaplus 268, apalache-mc 84, josehu07 35, pingcap 9, microsoft 6, TeamTilapia 1.
- **Per spec:** `spec_id`, `tla_path`, `repo`, `complexity_tier` (basic/intermediate/advanced),
  system/utility label, two natural-language descriptions (GPT + Claude) in two styles
  (declarative = translation, intent = design).
- **TLC counterexample traces** preserved in `data/dataset_manifest/tlc_logs/`.

## Files an external reviewer can open today
- Manifests: `data/dataset_manifest/{gold,gold_system,gold_utility,silver,silver_system}.json`
- Construction provenance: `data/dataset_manifest/README.json`, `drop_*.json` (every dropped spec listed)
- Vote records: `data/dataset_manifest/{gold,silver}_classification_voted.json` (per-model reasons)
- Results: `outputs/analysis/results_tables.md`, `construct_failure_map.md`
- Figures: `outputs/analysis/figures/{passk_curves,sany_by_tier,sany_pass1_by_model}.png`
