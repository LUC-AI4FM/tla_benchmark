| Experiment | Description source | Mode | Outputs | Archived SANY flag | sany_semantic_ok | Archived TLC | Qualified checked TLC |
|---|---|---|---:|---:|---:|---:|---:|
| A1 | GPT declarative | Configuration-aware | 100 | 91 | 74 | 22 | 15 |
| A2 | Claude declarative | Default | 100 | 89 | 77 | 31 | 23 |
| A3 | GPT declarative | Default, matched samples 0,1,2,3,4 | 500 | 449 | 390 | 93 | 63 |
| smoke | GPT declarative | Separate smoke | 1 | 1 | 0 | 0 | 0 |

| Sensitivity stratum | Tasks | A1 archived TLC / outputs | A2 archived TLC / outputs | A3 archived TLC / outputs |
|---|---:|---:|---:|---:|
| full_primary | 100 | 22/100 | 31/100 | 93/500 |
| with_original_configuration | 99 | 22/99 | 31/99 | 93/495 |
| without_missing_cfg_or_single_state_fixtures | 93 | 18/93 | 25/93 | 71/465 |
