from __future__ import annotations

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from utils import data_dir, get_logger, get_spec_by_id, outputs_dir, save_json, load_json
from validator import validate_spec

logger = get_logger("evaluate_ground_truth")

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--wandb-project", default="tla_bench", help="W&B project name")
    parser.add_argument("--wandb-entity", default=None, help="W&B entity (team/user)")
    args = parser.parse_args()

    import wandb
    run = wandb.init(
        project=args.wandb_project,
        entity=args.wandb_entity,
        name="ground_truth_eval",
        group="ground_truth_eval",
        job_type="eval",
        config={
            "model_id": "ground_truth",
        }
    )

    tla_dir = data_dir() / "tla_files"
    cfg_dir = data_dir() / "cfg"
    
    val_dir = outputs_dir() / "validation" / "ground_truth" / "original"
    val_dir.mkdir(parents=True, exist_ok=True)

    results = []
    
    spec_table = wandb.Table(columns=[
        "spec_id", "sany_pass", "tlc_pass"
    ])

    passed_sany = 0
    passed_tlc = 0
    total = 0

    try:
        if tla_dir.exists():
            for tla_file in tla_dir.glob("*.tla"):
                spec_id_str = tla_file.stem
                try:
                    spec_id = int(spec_id_str)
                except ValueError:
                    continue  # Not a spec_id integer
                
                spec_data = get_spec_by_id(spec_id)
                if spec_data is not None:
                    module_name = spec_data.get("ModuleName", str(spec_id))
                else:
                    module_name = str(spec_id)

                cfg_path = cfg_dir / f"{spec_id}.cfg"
                cfg_str = str(cfg_path) if cfg_path.exists() else None

                spec_tmp_dir = val_dir / spec_id_str
                spec_tmp_dir.mkdir(parents=True, exist_ok=True)
                tmp_tla = spec_tmp_dir / f"{module_name}.tla"
                
                # Copy original TLA to the named file for SANY to accept the internal MODULE <module_name> header
                with open(tla_file, "r") as src, open(tmp_tla, "w") as dst:
                    content = src.read()
                    dst.write(content)

                try:
                    summary = validate_spec(
                        tla_path=str(tmp_tla),
                        cfg_path=cfg_str,
                        validation_out_dir=str(val_dir),
                        spec_id=spec_id,
                        model_id="ground_truth",
                        condition="original"
                    )
                finally:
                    pass # Keep the temp file or clean it up if you want, but the val_dir handles outputs
                    
                sany_pass = summary.get("sany_pass", False)
                tlc_pass = summary.get("tlc_pass", False)
                
                results.append(summary)
                passed_sany += int(sany_pass)
                passed_tlc += int(tlc_pass)
                total += 1
                
                spec_table.add_data(spec_id, sany_pass, tlc_pass)
                
        if total > 0:
            wandb.log({
                "eval/overall_sany_rate": passed_sany / total,
                "eval/overall_tlc_rate": passed_tlc / total,
                "eval/total_specs": total,
                "results/spec_table": spec_table
            })
            
            logger.info("Ground truth overall sany_rate=%.3f tlc_rate=%.3f (%d specs)", passed_sany / total, passed_tlc / total, total)
        else:
            logger.warning("No TLA files found in %s", tla_dir)

    finally:
        run.finish()

    save_json(results, outputs_dir() / "run_ground_truth.json")

if __name__ == "__main__":
    main()
