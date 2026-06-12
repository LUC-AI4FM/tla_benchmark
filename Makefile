.PHONY: help test lint typecheck install \
        run-baselines run-hivemind run-preference-gen run-train-dpo run-train-sft \
        run-specprover run-analysis run-all \
        resume-baselines smoke-test clean-checkpoints clean

PYTHON  := python3
SRC     := src
TESTS   := tests

help:
	@echo ""
	@echo "tla+bench pipeline"
	@echo ""
	@echo "  make install              install all python dependencies"
	@echo "  make test                 run the full unit test suite"
	@echo "  make lint                 check syntax of all src/ files"
	@echo "  make smoke-test           quick 2-spec sanity check (no wandb)"
	@echo ""
	@echo "  make run-baselines        evaluate all 4 baseline models"
	@echo "  make run-hivemind         compute hivemind index"
	@echo "  make run-specprover       evaluate spec-prover (dpo)"
	@echo "  make run-analysis         generate dataset and results figures"
	@echo "  make run-all              run the full 4-step pipeline"
	@echo ""
	@echo "  make resume-baselines     continue an interrupted baseline run"
	@echo "  make clean-checkpoints    delete all checkpoint files"
	@echo "  make clean                delete all outputs and wandb local runs"
	@echo ""

install:
	$(PYTHON) -m pip install -r requirements.txt

lint:
	$(PYTHON) -m py_compile $(SRC)/*.py pipeline.py
	@echo "syntax ok"

test:
	$(PYTHON) -m pytest $(TESTS)/ -v --tb=short

typecheck:
	$(PYTHON) -m mypy $(SRC)/ --ignore-missing-imports --no-error-summary || true

run-baselines:
	$(PYTHON) pipeline.py --step baselines --workers 8

run-hivemind:
	$(PYTHON) pipeline.py --step hivemind

run-preference-gen:
	$(PYTHON) pipeline.py --step preference-gen

run-train-dpo:
	$(PYTHON) pipeline.py --step train-dpo --base-model $(BASE_MODEL)

run-train-sft:
	$(PYTHON) pipeline.py --step train-sft --base-model $(BASE_MODEL)

run-specprover:
	$(PYTHON) pipeline.py --step spec-prover

run-analysis:
	$(PYTHON) pipeline.py --step analysis

run-all:
	$(PYTHON) pipeline.py --workers 8

resume-baselines:
	$(PYTHON) pipeline.py --step baselines --workers 8 --resume

smoke-test:
	$(PYTHON) pipeline.py --step baselines --limit 2 --workers 2 \
	          --condition nlp_to_tla --no-wandb
	$(PYTHON) pipeline.py --step hivemind --no-wandb 2>/dev/null || true
	$(PYTHON) pipeline.py --step analysis --no-wandb
	@echo "smoke test complete."

clean-checkpoints:
	rm -rf outputs/checkpoints/
	@echo "checkpoints cleared."

clean:
	rm -rf outputs/checkpoints/ outputs/validation/ outputs/results/ outputs/logs/
	rm -rf outputs/run_*.json outputs/preference_*.jsonl outputs/sft_*.jsonl outputs/temp/
	rm -rf wandb/run-* wandb/debug*.log wandb/latest-run
	@echo "outputs and wandb local runs cleared."
