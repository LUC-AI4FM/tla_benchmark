# CLAUDE.md

## Project

TLA+Bench baseline evaluation. Run reasoning models against the TLA+Bench dataset to measure how well they generate TLA+ specifications from different input representations. Validate all outputs with SANY and TLC.

Make the below structure after analysizng the actual folders and copying files form them to here. 

## Repository Structure

```
baseline_eval/
├── CLAUDE.md
├── README.md
├── data/
│   ├── tla_files/              # 206 original .tla ground truth files
│   ├── v2_json/                # 206 verified 60-field JSON extractions
│   ├── v3_json/                # 206 extended 73-field JSON extractions
│   ├── descriptions/           # 206 natural language descriptions
│   └── test_split.json         # list of test spec IDs
├── configs/
│   ├── models.json             # model registry with endpoints and params
│   └── prompts/
│       ├── nlp_to_tla.txt      # prompt template: NLP description -> TLA+ spec
│       └── json_to_tla.txt     # prompt template: v3 JSON -> TLA+ spec
├── src/
│   ├── runner.py               # orchestrates model calls across conditions
│   ├── validator.py            # runs SANY and TLC on generated output
│   ├── parser.py               # extracts TLA+ code from model responses
│   ├── metrics.py              # computes pass rates and comparison tables
│   └── utils.py                # file I/O, logging, retry logic
├── outputs/
│   ├── raw/                    # full model responses per run
│   ├── extracted/              # cleaned .tla files extracted from responses
│   ├── validation/             # SANY and TLC results per run
│   └── logs/                   # full conversation logs (fine-tuning data)
└── results/
    ├── summary.csv             # aggregated pass rates per model per condition
    └── comparison.csv          # TLA+Bench vs published Lean/Coq numbers
```

## Core Rules

1. Never modify files in data/. They are read-only ground truth.
2. Every model response must be saved in full to outputs/raw/ before any processing.
3. Every generated .tla file must go through both SANY and TLC validation. No exceptions.
4. Conversation logs are a deliverable, not scratch work. Save complete input/output pairs.
5. No comments in code. No docstrings. Production-level, self-documenting names only.

## Dependencies

- Python 3.11+
- Java 11+ (for SANY and TLC)
- tla2tools.jar (download from https://github.com/tlaplus/tlaplus/releases)
- ollama (for local open-weight models)
- openai SDK (for GPT-4o, GPT-5)
- anthropic SDK (for Claude models, if used)

## Pipeline

### Step 1: Setup

Create the directory structure above. Place all dataset files in data/. Download tla2tools.jar and place it in the repo root.

Build configs/models.json with this structure:

```json
[
  {
    "id": "deepseek-r1-8b",
    "backend": "ollama",
    "model_name": "deepseek-r1:8b",
    "temperature": 0.0,
    "max_tokens": 8192
  },
  {
    "id": "qwen3-235b",
    "backend": "ollama",
    "model_name": "qwen3:235b",
    "temperature": 0.0,
    "max_tokens": 8192
  },
  {
    "id": "gpt-4o",
    "backend": "openai",
    "model_name": "gpt-4o",
    "temperature": 0.0,
    "max_tokens": 8192
  },
  {
    "id": "deepseek-prover-v1.5",
    "backend": "ollama",
    "model_name": "deepseek-prover-v1.5",
    "temperature": 0.0,
    "max_tokens": 8192
  }
]
```

### Step 2: Define Test Split

Load data/test_split.json. This file contains a list of spec IDs to evaluate. If it does not exist, create a random 20% stratified split from the 206 specs and save it.

### Step 3: Build Prompts

Two prompt templates in configs/prompts/:

**nlp_to_tla.txt** (Condition A: NLP description as input)

```
You are a TLA+ specification engineer. You will receive a natural language description of a system. Your task is to produce a complete, syntactically correct TLA+ specification that faithfully captures the described behavior.

Requirements:
- The output must be a valid TLA+ module that passes the SANY parser.
- Include the MODULE declaration, EXTENDS, CONSTANTS, VARIABLES, Init, Next, and Spec.
- Include all safety invariants and liveness properties described.
- Include fairness conditions if the description mentions them.
- Do not include any explanation. Output only the TLA+ specification.

System description:
{description}
```

**json_to_tla.txt** (Condition B: v3 JSON as input)

```
You are a TLA+ specification engineer. You will receive a structured JSON extraction of a TLA+ specification. The JSON contains the module name, constants, variables, operator definitions, action definitions, temporal properties, fairness conditions, and other constructs.

Your task is to reconstruct the complete TLA+ specification from this JSON.

Requirements:
- The output must be a valid TLA+ module that passes the SANY parser.
- Use every field in the JSON to produce the correct specification.
- Preserve the operator names, variable names, and constant names exactly as given.
- Do not include any explanation. Output only the TLA+ specification.

JSON extraction:
{json_content}
```

### Step 4: Run Experiments

For each model in configs/models.json:
  For each spec ID in test_split.json:
    For each condition (nlp_to_tla, json_to_tla):

1. Load the input (description or v3 JSON) from data/.
2. Fill the prompt template with the input.
3. Call the model API.
4. Save the full response to outputs/raw/{model_id}/{condition}/{spec_id}.json.
5. Extract the TLA+ code from the response using parser.py.
6. Save the extracted code to outputs/extracted/{model_id}/{condition}/{spec_id}.tla.
7. Run SANY on the extracted file. Save result to outputs/validation/.
8. If SANY passes, run TLC with the ground truth .cfg file. Save result to outputs/validation/.
9. Log the full conversation (input prompt + model response + validation results) to outputs/logs/.

Use progressive prompting for all runs. Break the generation into steps:
- Step 1: Generate module header, EXTENDS, CONSTANTS, VARIABLES.
- Step 2: Generate Init predicate.
- Step 3: Generate action operators and Next.
- Step 4: Generate Spec with temporal properties and fairness.
- Step 5: Combine all steps into final output.

Save each intermediate step in the conversation log.

### Step 5: Compute Metrics

After all runs complete, run metrics.py to produce:

**summary.csv**: One row per model per condition.
Columns: model_id, condition, total_specs, sany_pass, sany_rate, tlc_pass, tlc_rate.

**comparison.csv**: Cross-benchmark comparison.
Pull published numbers from the 144-paper survey JSON for the same models on miniF2F, PutnamBench, ProofNet.
Columns: model_id, minif2f_pass_rate, putnambench_pass_rate, tlabench_nlp_rate, tlabench_json_rate.

### Step 6: Error Analysis

For each failed run, categorize the error into one of five categories from prior work:
1. Unicode operator substitution (e.g., ∧ instead of /\)
2. Cross-language syntax injection (semicolons, curly braces, backticks)
3. Reasoning/formatting leakage (<think> blocks, markdown fences)
4. Generation length miscalibration (output >> expected length)
5. Structural errors (missing ==== terminator, duplicate MODULE headers)

Save error classifications to outputs/validation/{model_id}/{condition}/{spec_id}_errors.json.

## Code Standards

- No comments in source files.
- No docstrings.
- Function and variable names must be self-documenting.
- Type hints on all function signatures.
- All file I/O through utils.py.
- All API calls must have retry logic with exponential backoff.
- All subprocess calls (SANY, TLC) must have timeouts (60 seconds for SANY, 300 seconds for TLC).
- Exit code 0 from SANY means pass. Any other exit code means fail.
- TLC pass means exit code 0 and no "Error:" lines in stdout.
- Log every API call cost (tokens in, tokens out) for budget tracking.