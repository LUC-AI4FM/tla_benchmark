#!/usr/bin/env python3
"""
Evaluate Spec-Align with local Ollama models
Generates TLA+ specs for test cases and computes metrics
"""

import json
import subprocess
import sys
from pathlib import Path
from typing import Any
import logging

logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)

def call_ollama(model: str, prompt: str, timeout: int = None) -> str:
    """Call Ollama API to generate text"""
    try:
        result = subprocess.run(
            ["curl", "-X", "POST", "http://localhost:11434/api/generate",
             "-d", json.dumps({"model": model, "prompt": prompt, "stream": False})],
            capture_output=True,
            timeout=timeout
        )
        if result.returncode == 0:
            response = json.loads(result.stdout)
            return response.get("response", "")
        else:
            logger.error(f"Ollama error: {result.stderr.decode()}")
            return ""
    except Exception as e:
        logger.error(f"Connection error: {e}")
        return ""

def evaluate_ollama(
    model: str = "deepseek-r1:8b",
    num_specs: int = 5,
    output_file: str = "outputs/spec_align_results.json"
):
    """Generate specs using Ollama and collect results"""
    
    logger.info(f"Starting evaluation with {model}")
    logger.info(f"Generating specs for {num_specs} test cases")
    
    # Load test specs from preference dataset
    preferences = []
    with open("outputs/preference_dataset.jsonl") as f:
        for line in f:
            if line.strip():
                pref = json.loads(line)
                preferences.append(pref)
    
    results = []
    
    for i, pref in enumerate(preferences[:num_specs]):
        prompt = pref["prompt"]
        spec_id = pref.get("spec_id", i)
        
        logger.info(f"Generating spec {i+1}/{num_specs} (spec_id={spec_id})")
        
        # Generate using Ollama
        generated = call_ollama(model, prompt)
        
        # Extract TLA+ code (basic extraction)
        tla_code = generated
        if "MODULE" in generated:
            # Try to extract module
            try:
                start = generated.find("MODULE")
                end = generated.find("====", start)
                if end > start:
                    tla_code = generated[start:end+4]
            except:
                pass
        
        result = {
            "spec_id": spec_id,
            "model": model,
            "prompt": prompt[:100],
            "generated_length": len(generated),
            "tla_extracted": len(tla_code) > 50,
            "has_module_keyword": "MODULE" in generated,
            "timestamp": str(__import__('datetime').datetime.now())
        }
        
        results.append(result)
        logger.info(f"  Generated {len(generated)} chars, TLA extracted: {result['tla_extracted']}")
    
    # Save results
    output_path = Path(output_file)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2)
    
    logger.info(f"\n✓ Evaluation complete!")
    logger.info(f"✓ Results saved to {output_path}")
    logger.info(f"✓ Generated {len(results)} specs")
    
    # Compute metrics
    has_module = sum(1 for r in results if r["has_module_keyword"])
    tla_extracted = sum(1 for r in results if r["tla_extracted"])
    
    logger.info(f"\nMetrics:")
    logger.info(f"  Specs with MODULE keyword: {has_module}/{len(results)} ({100*has_module//len(results)}%)")
    logger.info(f"  TLA code extracted: {tla_extracted}/{len(results)} ({100*tla_extracted//len(results)}%)")
    
    return results

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", default="deepseek-r1:8b")
    parser.add_argument("--num-specs", type=int, default=5)
    parser.add_argument("--output", default="outputs/spec_align_results.json")
    
    args = parser.parse_args()
    
    evaluate_ollama(
        model=args.model,
        num_specs=args.num_specs,
        output_file=args.output
    )
