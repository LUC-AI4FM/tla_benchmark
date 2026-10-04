#!/usr/bin/env python3
"""Build a source-grounded review packet without candidate/model/provider labels.

The packet is for independent human assessment, not simulated human evidence.
Contracts come from frozen references and original configurations. It is a
post-generation validation packet, not a preregistered assessment.
"""
import argparse
import hashlib
import json
from pathlib import Path

import reproduce as E


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--private-key", required=True, type=Path,
                        help="store provider/task assignment separately from the blind packet")
    args = parser.parse_args()
    E.verify()
    manifest = {str(r["spec_id"]): r for r in map(json.loads, (E.REPO / "manifest.jsonl").read_text().splitlines())}
    packets, keys = [], []
    for sid in E.load(E.REPO / "outputs/eval_100_ids.json"):
        sid = str(sid)
        ref = next((E.REPO / "specs/gold").glob(sid + "_*.tla"))
        cfg = ref.with_suffix(".cfg")
        digest = E.sha(ref)
        case_id = hashlib.sha256(("description-review:" + digest).encode()).hexdigest()[:20]
        order = ["desc_declarative_gpt", "desc_declarative_claude"]
        if int(digest[:2], 16) % 2:
            order.reverse()
        packets.append({"case_id": case_id, "reference_sha256": digest,
                        "original_configuration_sha256": E.sha(cfg) if cfg.exists() else None,
                        "reference_contract_path": str(ref.relative_to(E.REPO)),
                        "original_configuration": cfg.read_text() if cfg.exists() else None,
                        "description_A": manifest[sid][order[0]], "description_B": manifest[sid][order[1]],
                        "assessment_phase": "post_generation_validation_of_frozen_reference_contract",
                        "human_review_status": "unreviewed", "human_equivalence_assessment": None,
                        "human_notes": None})
        keys.append({"case_id": case_id, "spec_id": sid, "A": order[0], "B": order[1]})
    args.output.write_text("\n".join(json.dumps(p, ensure_ascii=False) for p in packets) + "\n")
    args.private_key.write_text(json.dumps(keys, indent=2) + "\n")
    print(f"Prepared {len(packets)} unreviewed cases; assignments are in the separate private key.")


if __name__ == "__main__":
    main()
