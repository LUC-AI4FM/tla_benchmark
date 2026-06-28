# Paper Plan: Contamination-Controlled Evaluation of LLM TLA+ Generation

This file is the plan for our next paper. Read it and confirm if the direction
and the experiment list look good before we start running things.

Last updated: 2026-06-27

---

## 1. The short version

We are writing a paper that asks one question: when an LLM appears to write a
correct TLA+ specification, is it actually reasoning, or is it just recalling a
spec it saw on public GitHub during training?

Our group already published two papers in this area. This paper builds directly
on them and fills a gap that both of them left open: neither one checked for
data contamination (memorization). We will measure how much of the reported
ability is real derivation versus memorization, show where the memorization
lives, and test whether fine-tuning teaches real reasoning or just deepens
memorization.

Target venue: AAAI-27. Abstract deadline July 20, 2026. Paper deadline July 27,
2026. That is about four weeks from now.

---

## 2. Why this paper, and why now

### What already exists (the competition, including our own group)

1. FormaLLM (our group, "Can LLMs Write Correct TLA+ Specifications?").
   Evaluated 30 LLMs on 205 specs, graded with SANY plus TLC. Reports up to
   26.6 percent syntax and 8.6 percent semantic correctness. It does NOT discuss
   contamination or memorization at all. Its future-work section asks for
   fine-tuning and repair loops.

2. TLA-Prover (our group). Fine-tunes gpt-oss-20b with LoRA plus repair-GRPO and
   reaches 30 percent pass. Its only contamination control is using "disjoint
   module names" on a 30-problem holdout. It does NOT run a real
   perturbation or memorization test. It is weak on quantifiers and case
   analysis, which it admits.

3. SysMoBench (ICLR 2026, different group). TLA+ benchmark on 11 real systems
   with SANY, TLC, trace conformance, and invariant checks. Uses public systems,
   so it is maximally contaminated, and it does not control for that.

### The gap

None of these three papers controls for contamination. The broader code-LLM
field has shown that this matters a lot: supervised fine-tuning raises accuracy
but also introduces memorization, and benchmarks like HumanEval are heavily
contaminated. That contamination work has been done for ordinary code (Python,
HumanEval, MBPP) but NOT for formal specifications or TLA+. So formal methods is
open territory for this exact question.

### Our advantage

We already built the hard part: a semantics-preserving perturbation tool that
renames every user identifier consistently across the spec, its config, and its
dependent modules, then re-verifies with SANY plus TLC. This is stronger than
TLA-Prover's "rename the module name only" control. We also already have the
clean and perturbed frontier results that prove the effect is real.

---

## 3. The core finding we already have

On Claude Opus 4.8, over 111 matched specs that stay valid after renaming:

- Clean (original specs): 98.2 percent parse, 28.8 percent fully correct.
- Perturbed (renamed specs): 97.3 percent parse, 15.3 percent fully correct.

So parsing barely moves, but correctness nearly halves once you remove the
memorizable surface form. That 28.8 to 15.3 drop is the seed of the whole paper.
It says roughly half of the apparent ability is memorization and half is real
derivation.

---

## 4. The thesis (one sentence)

Reported LLM success on TLA+ generation is inflated by memorization of public
specifications, and once you control for it with full semantics-preserving
perturbation, real reasoning ability is much lower, concentrated in safety
properties, and only partly improved by fine-tuning.

---

## 5. The three contributions

### Contribution 1: Contamination measurement

Measure the clean-versus-perturbed correctness gap across many models (frontier
and open). Produce a memorization-versus-derivation table and chart. This is the
first contamination-controlled evaluation of TLA+ generation.

### Contribution 2: Where the memorization lives

Break the perturbation effect down by construct type. Our earlier construct map
shows all correct answers were safety properties, and temporal, liveness,
fairness, and quantifier specs fail almost completely. We will show that what
survives perturbation is concentrated in safety properties, and that the
temporal and liveness failures are genuine reasoning failures rather than just
missing memorized text. This connects contamination to the capability cliff and
directly addresses TLA-Prover's admitted weakness on quantifiers.

### Contribution 3: Fine-tuning as a probe, not a score chase

Re-run a fine-tuning recipe close to TLA-Prover (SFT, and optionally DPO, on
TLC-passing specs), then evaluate the fine-tuned model on the PERTURBED test set,
not just the clean one. The question is not "does fine-tuning raise the score"
because TLA-Prover already showed it does. The question is "does fine-tuning
teach derivation or deepen memorization." If the fine-tuned model gains on clean
specs but not on perturbed specs, it memorized. The general code literature
predicts exactly this, and nobody has shown it for formal methods.

---

## 6. What we already have built (assets)

- Cleaned dataset: 403 gold specs (parse plus model-check) and 897 silver specs
  (parse only), from 9 GitHub repos, with audited cleaning and 3-model voting for
  labels. This is larger than FormaLLM's 205.
- Execution-grounded grading harness (SANY plus TLC), with the config-binding bug
  fixed.
- Frontier baselines: Opus 4.8 (98 percent parse, 23 percent correct) and Sonnet
  4.6 (82 percent parse, 14 percent correct).
- Open-model baselines: qwen, llama, gpt-oss, and others around 1 to 2 percent.
- The full perturbation tool, verified on 111 of 146 gold specs (76 percent stay
  valid after renaming).
- Perturbed descriptions generator and a perturbed evaluation mode in the runner.
- The contamination result on Opus 4.8 (the 28.8 to 15.3 drop).
- SFT, LoRA, and DPO trainer code (written but never run yet).
- Natural-language descriptions in two styles (declarative and intent) from two
  providers (GPT and Claude).

So most of the paper is runs and writing, not new inventions.

---

## 7. The experiment plan (four weeks)

### Week 1: Make Contribution 1 real (the multi-model contamination table)

Goal: turn the single Opus result into a table across many models.

- Run the perturbed evaluation on more models, both clean and perturbed, on the
  111 verified specs:
  - Frontier (API, uses the Anthropic and OpenAI keys): Claude Sonnet 4.6,
    Claude Opus 4.8 (done), and if budget allows one OpenAI model.
  - Open (your GPUs): qwen2.5-coder-32b, llama3.3-70b, gpt-oss-20b, and a couple
    more.
- Add pass-at-k (for example k equals 5 or 10) on both clean and perturbed so the
  gap has confidence intervals, not single-run noise.
- Tighten the perturbation tool to recover the 8 specs that failed SANY after
  renaming, to push retention above 76 percent.

Output: one table and one figure showing clean correctness, perturbed
correctness, and the drop, per model.

### Week 2: Contribution 2 (where recall lives) plus reviewer-proofing

Goal: depth and credibility.

- Break the clean-versus-perturbed drop down by construct type (safety, temporal,
  liveness, fairness, quantifiers). Show survivors cluster in safety.
- Characterize the temporal and liveness failures with concrete examples, since
  this is the part no model solves and it is real reasoning failure.
- Build a small human-verified description subset (50 to 100 specs) so we can say
  the result is not an artifact of LLM-written descriptions. This closes a known
  reviewer objection.

Output: a per-construct breakdown table, a short qualitative failure analysis,
and a human-verified subset note.

### Week 3: Contribution 3 (fine-tuning probe)

Goal: run the fine-tuning and evaluate it the new way.

- Use the existing SFT plus LoRA code. Base model: gpt-oss-20b (same family as
  TLA-Prover so the comparison is fair) or another open model we can train on the
  GPUs.
- Training data: our gold TLC-passing specs, paired with their descriptions.
- Evaluate the fine-tuned model on BOTH the clean test set and the perturbed test
  set.
- Optional: the DPO variant if time allows.
- The key plot: fine-tuning gain on clean versus gain on perturbed. If clean goes
  up but perturbed does not, that is the memorization result.

Output: a before-and-after table for the fine-tuned model on clean and perturbed,
and the gain-comparison plot.

### Week 4: Write and polish

- Assemble the paper in AAAI two-column format (about 7 pages plus references).
- Reuse the dataset card, results tables, and figures already in
  outputs/analysis.
- Cite and build on FormaLLM and TLA-Prover explicitly. Frame as extending our
  group's line of work, not competing with it.
- Buffer time for the abstract on July 20 and the paper on July 27.

---

## 7b. Work completed so far (full record as of 2026-06-27)

This section is the running log of what has actually been done, so the state is
clear at a glance. Items marked DONE are finished and saved; items marked RUNNING
are executing on the GPU machine right now.

### Data collection and cleaning (DONE)

- Pulled 1,614 real TLA+ specification files from 9 public GitHub repositories
  (tlaplus, apalache-mc, microsoft, pingcap, Azure, atomix, tendermint, josehu07,
  TeamTilapia).
- Ran every file through SANY (parser) and TLC (model checker) with tla2tools.jar.
- Audited cleaning funnel, dropped 213 files: 88 that fail to parse, 68
  negative-test and tooling files that are intentionally broken, 42 test fixtures,
  15 with runtime errors. Each dropped file is recorded in
  data/dataset_manifest/drop_*.json.
- Discovered and handled a real trap: the raw corpus contained deliberately broken
  test fixtures that would have polluted the benchmark if left in.

### Final dataset (DONE)

- 403 gold specs (parse and model-check), split 146 system and 257 utility.
- 897 silver specs (parse only, no runnable config).
- Each spec tagged with a complexity tier (basic, intermediate, advanced) and a
  system-versus-utility label.
- Labels assigned by a 3-model vote (llama3.3, qwen2.5-coder, gpt-oss); 91 percent
  unanimous on gold. Vote records saved with per-model reasons.
- TLC counterexample traces preserved.
- Dataset card written at outputs/analysis/DATASET_CARD.md.

### Task descriptions (DONE)

- Generated natural-language descriptions for each spec in two styles: declarative
  (translation, names leak so TLC can grade exactly) and intent (design, names
  hidden, graded parse-only for now).
- Two providers: GPT and Claude. Validated by cross-model agreement, not by
  round-trip generation.

### Grading harness (DONE)

- Built an execution-grounded grader: a model passes only if its generated spec
  parses with SANY and model-checks with TLC. Never text similarity.
- Fixed a real bug: configs bind to specs by name and most gold dirs have more
  than one config, so the config had to be bound by the original spec stem,
  otherwise TLC never ran. scripts/run_baseline.py.

### Baseline results (DONE)

- Open models, declarative gold (n=146): qwen2.5-coder-32b 24.0 percent SANY /
  1.4 percent TLC, llama3.3-70b 19.2 / 1.4, gpt-oss-20b 4.8 / 0.0, and several
  others at or near zero (gemma, mistral, llama3.2-3b, deepseek-coder,
  deepseek-prover).
- Pass@1, pass@5, pass@10 (n=10 sampling) for qwen, llama, gpt-oss: SANY climbs
  with retries (qwen reaches 64 percent SANY at pass@10) but TLC stays low (about
  2 to 5 percent). So syntax is solvable with retries, correctness is the wall.
- Construct-level failure map: every correct answer was a safety property.
  Temporal, liveness, fairness, and quantifier specs fail almost completely. Saved
  at outputs/analysis/construct_failure_map.md.

### Frontier results (DONE)

- Added Claude Opus 4.8 and Sonnet 4.6 (fixed the API call to drop temperature,
  which these models reject). These are open-source-paper reference rows only; no
  ongoing API spend.
- Opus 4.8: 97.9 percent SANY, 23.3 percent TLC. Sonnet 4.6: 81.5 percent SANY,
  13.7 percent TLC. About 17 times the best open model on correctness.
- Key reframe: the earlier "models only get about 1 to 5 percent correct" story
  was an open-model artifact. The real shape is a capability cliff, and the
  benchmark now has dynamic range from 0 to about 23 percent, which lets it
  discriminate models.

### Perturbation tool and contamination result (DONE)

- Built a semantics-preserving perturbation tool that renames every user
  identifier (module, constants, variables, operators) consistently across the
  spec, its config, and dependent modules, then re-verifies with SANY and TLC.
  This is stronger than TLA-Prover's module-name-only control.
  scripts/analysis/perturb_spec.py.
- Ran it across all 146 gold-system specs: 111 (76 percent) stay valid after
  renaming. Median surface similarity to the original drops to about 0.81.
  outputs/analysis/perturb_gold_system_full.json.
- Built the perturbed-description generator and a perturbed evaluation mode in the
  runner. data/descriptions_perturbed/, run_baseline.py --perturbed.
- Contamination result on Opus 4.8 (matched 111 specs): clean 28.8 percent TLC
  versus perturbed 15.3 percent TLC. Parsing barely moved (98.2 to 97.3 percent).
  So correctness nearly halves once the memorizable surface form is removed. This
  is the seed result for the whole paper.

### Counterexample method (TESTED AND DROPPED)

- Built a parser for TLC counterexample traces and a repair loop that feeds the
  trace back to the model. src/counterexample.py, scripts/ce_repair.py.
- Go/no-go test: counterexample feedback versus plain "it is wrong" feedback.
  Result was flat on both open models (qwen) and frontier (Opus 4.8): about 36
  percent versus 34 percent. No signal. The method is dropped and is not part of
  the paper.

### Fine-tuning code (WRITTEN, NEVER RUN YET)

- src/sft_trainer.py (SFT with LoRA), src/dpo_trainer.py,
  src/preference_generator.py exist and are ready. No model has been trained yet.
  No trained weights exist anywhere in the repo. This is Week 3 work.

### Currently running on the GPU machine (RUNNING)

- Greedy contamination runs: clean and perturbed evaluation for qwen2.5-coder-32b,
  llama3.3-70b, and gpt-oss-20b on the 111 verified specs.
  outputs/contamination/.
- Pass@10 contamination runs (n=10 at temperature 0.7) for the same three models,
  clean and perturbed, queued to start when the greedy runs finish. This gives the
  contamination drop confidence intervals and keeps k=10 consistent with our
  earlier experiments. outputs/contamination_passk/.

### Early observation to watch

- On the matched 111-spec subset the open models look weak (qwen about 31 percent
  SANY, 2 percent TLC greedy). They may be too close to the floor to show a large
  contamination drop. If so, the clean contamination signal lives mainly in the
  frontier reference rows (Opus and Sonnet), and the open-source contamination
  story leans more on the fine-tuning probe, where the trained model gains
  capability that can then be perturbation-tested. Pass@10 will tell us if retries
  lift the open models off the floor.

---

## 8. What we will NOT do (scope control)

- We will not try to beat TLA-Prover's score. Our fine-tuning is a probe, not a
  competition.
- We will not invent a new training method. The counterexample-guided idea tested
  flat (36 percent versus 34 percent), so it is dropped. We will not build on it.
- We will not chase the intent (design) track correctness. It stays parse-only
  for now, as decided earlier.
- We will not expand to other formal languages. TLA+ only.

---

## 9. Risks and how we handle them

- Risk: the contamination drop shrinks on other models, so the effect looks weak.
  Handling: report it honestly across models. Even a model-dependent effect is a
  finding, and Opus already shows a large drop.
- Risk: fine-tuning does not converge well on the GPUs in time.
  Handling: SFT alone is enough for the probe. DPO is optional. We can also use a
  smaller base model if needed.
- Risk: reviewers say the dataset overlaps with FormaLLM.
  Handling: ours is larger (403 vs 205) and from 9 repos, and the contribution is
  the contamination control, not the dataset itself.
- Risk: four weeks is tight.
  Handling: Contribution 1 alone (the multi-model contamination table) plus the
  construct breakdown is already a paper. Fine-tuning is the strongest leg but is
  the one we drop first if time runs out.

---

## 10. The minimum viable paper

If everything slips, the paper still stands on Contribution 1 plus Contribution
2: a multi-model contamination-controlled re-evaluation of TLA+ generation, with
a per-construct breakdown, showing that reported numbers are inflated by
memorization and that temporal reasoning is a real wall. That alone is novel for
formal methods and is a solid AAAI submission. Contribution 3 (fine-tuning probe)
makes it stronger if time allows.

---

## 11. Headline sentence for the abstract

On a model-checked TLA+ benchmark, frontier models appear correct on up to about
a quarter of specifications, but under semantics-preserving renaming that drops
by nearly half, revealing that much of the apparent ability is memorization of
public specifications, that what survives is concentrated in safety properties,
and that fine-tuning largely deepens memorization rather than teaching the
temporal reasoning where all models still fail.

---

## 12. Locked decisions (confirmed 2026-06-27)

These were decided based on our own baseline numbers and the code-LLM
memorization literature.

- Open source only. No API spend. The frontier Opus and Sonnet results we already
  have stay in as a "frontier reference" row, but open-source models are the main
  story. This also makes the paper fully reproducible, which is a plus for a
  contamination paper.

- Contamination-study models (chosen from our baselines, which show a clear
  split): qwen2.5-coder-32b (best open parser, 21.4 percent SANY), llama3.3-70b
  (17.0 percent SANY, different family), and gpt-oss-20b (6.4 percent SANY, and
  it is TLA-Prover's base model). Everything else in our baselines sits near zero
  SANY (gemma, mistral, llama3.2-3b, deepseek-coder, deepseek-prover), so it only
  shows zeros. Those go in an appendix, not the main table. The Opus and Sonnet
  numbers are the frontier reference rows.

- Fine-tuning base model: gpt-oss-20b. Same base as TLA-Prover, so our "does
  fine-tuning memorize" probe is a direct and fair extension of our group's own
  result.

- Fine-tuning is kept (Contribution 3 stays). We will train TWO fine-tuned
  models, following the accepted methodology in the code-LLM memorization
  literature (for example "Memorize or Generalize?", arXiv 2503.02296, and
  "Improving Robustness via Fine-tuning with Perturbed Data", arXiv 2602.11411):
  1. Clean-trained model: train on clean specs, evaluate on clean AND perturbed.
     If clean accuracy rises but perturbed does not, that gap is memorization.
  2. Perturbation-aware model: train on perturbed data too, then show it keeps
     accuracy while lowering the memorization gap. This is the "and here is the
     fix" result that turns the paper from a critique into a contribution.
  We will report the literature's metrics: a memorization risk index and a
  robustness-degradation measure (clean accuracy minus perturbed accuracy), so
  our numbers are directly comparable to the code-LLM work.

- Framing upgrade: we are importing the code-LLM memorization methodology
  (perturbation testing, robustness degradation, perturbation-aware fine-tuning)
  into formal methods for the first time, and showing it applies to TLA+ and to
  our group's own fine-tuning recipe.

## 13. Authorship note

You are the author of both FormaLLM and TLA-Prover. So this is your own next
paper, not a competing one. That means:

- We reuse your own assets directly: FormaLLM's dataset and findings, and
  TLA-Prover's training pipeline (SFT plus LoRA plus repair-GRPO, base
  gpt-oss-20b, the diamond and gold validation tiers). No reimplementation and no
  coordination needed.
- The framing is self-critique, which is stronger, not weaker: we revisit our own
  published numbers and stress-test them under full perturbation, and find they
  were partly inflated by memorization. That reads as rigor.
- We can state precisely what the prior controls were and why they are not
  enough: FormaLLM did not control for contamination at all, and TLA-Prover only
  swapped module names on its holdout. Our full perturbation renames module,
  constants, variables, operators, the config, and dependent modules.
- The fine-tuning leg becomes a clean extension of TLA-Prover: take the same
  recipe and run it through the perturbation test it never had, to see how much
  of its gain survives.

Final build decisions (confirmed 2026-06-27):

- Fine-tuning code: the src/ trainers in this repo (sft_trainer.py and
  dpo_trainer.py). Self-contained, everything in one place.
- Main dataset: this repo's 403 gold specs (146 system, 257 utility), not
  FormaLLM's 205. It is bigger, from 9 repos, and the perturbation set (111
  verified) is already built on it. The contamination story does not need to match
  the old set.

Venue and framing decisions (confirmed 2026-06-27, after reading the AAAI-27 CFP):

- Track: AAAI-27 Main Technical Track. The CFP explicitly accepts "critical"
  contributions (principled analyses that draw attention to problematic
  assumptions) and says it prefers papers that introduce new problems or point out
  new directions over incremental state-of-the-art gains. Our paper fits that
  preferred profile.
- Key dates (Main Track): abstract due July 21, 2026; full paper due July 28,
  2026; supplementary material and code due July 31, 2026. All anywhere-on-earth
  (UTC-12). Two-phase review; 7 pages main content, up to 9 with references.
  Reproducibility checklist required.
- Headline novelty to lead with: the model checker gives an EXACT
  ground-truth correctness oracle, so we can measure memorization with real
  correctness, not the fuzzy similarity heuristics that prior code-LLM
  contamination work relies on. This is the differentiator that makes it more than
  "contamination methods applied to TLA+." Frame the finding as about LLM
  reasoning in general (models fake formal reasoning via surface memorization, and
  it collapses on temporal logic), with TLA+ as the clean testbed.
- Self-novelty risk: the CFP names self-plagiarism as an ethics violation and runs
  a novelty check across submissions with overlapping authors. Since we authored
  FormaLLM and TLA-Prover, the related-work section must be thorough and
  unambiguous: state plainly that this paper reuses the benchmark and the
  fine-tuning recipe from our prior work, and contributes the contamination
  control, the model-checker-oracle measurement, and the perturbation-aware fix
  that neither prior paper did. Handled in related work (not a standalone section),
  but written strongly enough to defuse a desk-reject risk.
