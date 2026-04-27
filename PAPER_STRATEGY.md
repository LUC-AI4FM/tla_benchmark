# NeurIPS Paper Strategy: TLA-Bench

This document outlines the strategy for positioning our TLA+ benchmark project for submission to a top-tier conference like NeurIPS. It is based on a combined analysis of three successful NeurIPS 2025 papers: "WebGen-Bench", "Artificial Hivemind", and "InterMT".

## 1. Core Contributions & Narrative

- **[✓] Title:** **TLA-Bench: A Programmatic Benchmark for Formal Verification Reasoning**
- **[✓] Narrative:** Formal verification is a critical domain where correctness is paramount. We introduce **TLA-Bench**, the first benchmark to systematically probe the logical reasoning of LLMs using **Programmatically Verifiable Preferences (PVP)**. We find that models exhibit a **'Logical Hivemind'**, developing shared blind spots in reasoning. We demonstrate our benchmark's value by creating **Spec-Align**, a model fine-tuned with Direct Preference Optimization (DPO) that significantly outperforms base models, proving our PVP data is a powerful tool for teaching models true logical reasoning.

---

## 2. Methodology & Evaluation Plan

### [✓] The Contribution Formula
- **[✓] Benchmark:** `TLA-Bench` (test set)
- **[✓] Training Data:** `TLA-Instruct` (training set derived from the main corpus)
- **[✓] Fine-Tuned Model:** `Spec-Align`

### [✓] The Analytical Narrative
- **[✓] Core Concept:** Frame the analysis around the **"Logical Hivemind"** hypothesis.
- **[✓] Core Method:** Leverage **Programmatically Verifiable Preferences (PVP)** using SANY and TLC as objective, scalable arbiters of correctness.

### [✓] The Alignment Method
- **[✓] Algorithm:** Use **Direct Preference Optimization (DPO)** to train `Spec-Align`.
- **[✓] Data Format:** The `(prompt, chosen_spec, rejected_spec)` triplets from our PVP pipeline are the exact input format for DPO.

### [✓] Evaluation Metrics
- **[✓] ML & AI Metrics:**
    - **Pass Rate (Pass@k):** Primary metric for syntactic (SANY) and semantic (TLC) correctness.
    - **CodeBLEU/CrystalBLEU:** Measure structural and syntactic similarity to the ground-truth using Abstract Syntax Trees (ASTs).
    - **Preference Accuracy:** Evaluate the model's ability to distinguish `chosen` vs. `rejected` outputs.
- **[✓] Software Engineering Metrics:**
    - **Cyclomatic Complexity:** Measure the complexity of the logical structure.
    - **Halstead Complexity Measures:** Quantify the specification's size, vocabulary, and effort to understand.
    - **Maintainability Index (MI):** A composite score for overall code quality.

---

## 3. Technical Implementation Plan

This section details the concrete technical tasks required to execute the research plan.

**Phase 1: Data Preparation & Partitioning**
- **Task:** Write a script (`src/partition_dataset.py`) to split the 206 specifications.
- **Details:**
    - **`TLA-Bench` (Test Set):** Select ~50 diverse specifications covering a wide range of constructs. This set will be held out and used exclusively for evaluation.
    - **`TLA-Instruct` (Training Set):** The remaining ~156 specifications will be used to generate prompts and preference pairs for model training.
- **Status:** To-Do

**Phase 2: Baseline Model Evaluation & Analysis**
- **Task:** Run all baseline LLMs against the prompts generated from `TLA-Bench`.
- **Details:**
    - Use `src/runner.py` to generate multiple outputs (`k=5`) for each prompt.
    - Store all raw outputs in the `outputs/raw/` directory.
- **Status:** To-Do
- **Task:** Implement the failure analyzer.
- **Details:**
    - Create `src/analyzer.py` to parse SANY and TLC error messages.
    - The script should categorize errors (e.g., "Syntax Error: Expecting `)`", "Temporal Error: Liveness property violated").
    - This provides the data for the "Logical Hivemind" analysis.
- **Status:** To-Do

**Phase 3: PVP Data Generation**
- **Task:** Process the raw outputs to create the `(prompt, chosen, rejected)` preference triplets.
- **Details:**
    - Use `src/validator.py` to run SANY and TLC on all generated outputs.
    - For each prompt, identify one `chosen` (SANY+TLC pass) and at least one `rejected` (SANY or TLC fail) output.
    - Store the final preference dataset in `data/pvl_pairs.json`.
- **Status:** To-Do

**Phase 4: `Spec-Align` Training**
- **Task:** Set up and run the Direct Preference Optimization (DPO) training pipeline.
- **Details:**
    - Use a library like `trl` (Transformer Reinforcement Learning) from Hugging Face.
    - The input will be the `data/pvl_pairs.json` dataset.
    - The base model will be a strong open-source model (e.g., DeepSeek-Coder, CodeLlama).
    - The output will be the fine-tuned `Spec-Align` model weights.
- **Status:** To-Do

**Phase 5: Final Evaluation & Results Generation**
- **Task:** Evaluate `Spec-Align` on the `TLA-Bench` test set.
- **Details:**
    - Run `Spec-Align` on the same prompts used for the baseline models.
    - Apply all ML and SWE metrics defined in the `Evaluation Metrics` section.
- **Status:** To-Do
- **Task:** Generate figures and tables for the paper.
- **Details:**
    - Create the "Logical Hivemind" heatmap showing failure rates across models.
    - Create comparison tables for Pass@k, CodeBLEU, and SWE metrics.
- **Status:** To-Do

---

## 4. Action Plan

**Completed Tasks:**
- **[✓]** Refined paper narrative, title, and abstract.
- **[✓]** Established names for the benchmark (`TLA-Bench`) and model (`Spec-Align`).
- **[✓]** Cloned Overleaf project for direct editing.
- **[✓]** Justified the use of DPO.
- **[✓]** Outlined a comprehensive set of ML and SWE evaluation metrics.
- **[✓]** Added Methodology section to the paper detailing PVP, DPO, and Evaluation Metrics.

**Immediate To-Do List:**
1.  **Implement `partition_dataset.py`:** Formally partition the data into `TLA-Bench` and `TLA-Instruct`.
2.  **Implement `analyzer.py`:** Create the script to categorize SANY/TLC failure modes.
3.  **Run Baseline Evaluation:** Generate outputs from base models for the `TLA-Bench` prompts.
4.  **Build `Spec-Align`:** Set up the DPO training pipeline and train the model.
5.  **Draft Experiments/Results:** Continue drafting the paper with the generated results.

This updated strategy is comprehensive and aligns with the highest standards of NeurIPS. We now have a clear path to a top-tier publication.
