#!/bin/bash

set -e

echo "TLA-Bench Quick Start Setup"
echo "==========================="
echo ""

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

echo "1. Installing dependencies..."
pip install -q -r requirements.txt
echo "   ✓ Dependencies installed"
echo ""

echo "2. Checking TLA+ tools..."
if [ ! -f "tla2tools.jar" ]; then
    echo "   ⚠ tla2tools.jar not found"
    echo "   Download from: https://github.com/tlaplus/tlaplus/releases"
    echo "   Place in: $REPO_ROOT"
else
    echo "   ✓ tla2tools.jar found"
fi
echo ""

echo "3. Verifying data files..."
if [ ! -f "data/test_split.json" ]; then
    echo "   ✗ data/test_split.json not found"
    exit 1
fi
if [ ! -d "data/v2_json" ] || [ -z "$(ls -A data/v2_json)" ]; then
    echo "   ✗ data/v2_json is empty"
    exit 1
fi
echo "   ✓ Data files OK"
echo ""

echo "4. Testing imports..."
python3 -c "
import sys
sys.path.insert(0, 'src')
from runner import _call_model
from preference_generator import generate_preference_dataset
from dpo_trainer import train_dpo_model
from evaluation import SpecificationEvaluator
from orchestrator import PipelineOrchestrator
print('   ✓ All imports successful')
"
echo ""

echo "5. Creating output directories..."
mkdir -p outputs/logs
mkdir -p outputs/validation
mkdir -p outputs/dpo_models
mkdir -p outputs/evaluation
mkdir -p results
echo "   ✓ Directories created"
echo ""

echo "Setup complete!"
echo ""
echo "Quick start examples:"
echo "  python src/preference_generator.py --limit 5 --candidates 3"
echo "  python src/dpo_trainer.py --base-model gpt2 --train-dataset outputs/preference_dataset.jsonl"
echo "  python src/evaluation.py --comparison"
echo "  python src/orchestrator.py --stage full --limit 5 --skip-training"
echo ""
