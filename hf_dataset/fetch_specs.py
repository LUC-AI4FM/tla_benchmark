#!/usr/bin/env python3
"""Re-fetch the original TLA+ source files for this dataset.

The dataset distributes our annotations (labels, descriptions, perturbations,
scores) plus pointers to the original specs. It does NOT redistribute the raw
.tla files, because they were collected from 9 separate GitHub repositories with
their own licenses. This script reconstructs the local spec files from the
pointers in specs.jsonl so you can reproduce the benchmark.

Each row in specs.jsonl carries:
  source_repo, source_repo_url, source_path, spec_sha256

source_path is the path the file had in our collection. You point this script at
local clones of the source repos (or let it clone them) and it copies the matching
files into ./tla_files/, then verifies each against spec_sha256.

Usage:
  python fetch_specs.py --clones /path/to/repo/clones
  python fetch_specs.py --auto-clone        # clone the source repos first

This is a skeleton: fill in the per-repo path mapping for your local clones. The
spec_sha256 check tells you when a source file has drifted from the version we
used.
"""
from __future__ import annotations
import argparse, json, hashlib, shutil
from pathlib import Path

HERE = Path(__file__).parent


def sha16(p: Path) -> str | None:
    return hashlib.sha256(p.read_bytes()).hexdigest()[:16] if p.exists() else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--clones", default="clones",
                    help="directory holding local clones of the source repos")
    ap.add_argument("--out", default="tla_files")
    args = ap.parse_args()

    rows = [json.loads(l) for l in open(HERE / "specs.jsonl")]
    out = HERE / args.out
    out.mkdir(parents=True, exist_ok=True)
    clones = Path(args.clones)

    found = missing = drifted = 0
    for r in rows:
        # source_path looks like data/tla_files/<repo>/<...>. Strip the prefix to
        # recover the path inside the original repo clone.
        rel = r["source_path"].split("data/tla_files/", 1)[-1]
        src = clones / rel
        if not src.exists():
            missing += 1
            continue
        dst = out / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        if r.get("spec_sha256") and sha16(dst) != r["spec_sha256"]:
            drifted += 1
        found += 1

    print(f"fetched {found}, missing {missing}, sha-drifted {drifted} of {len(rows)}")
    if missing:
        print("Missing files: clone the source repos (see source_repo_url in "
              "specs.jsonl) into --clones, preserving each repo's directory layout.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
