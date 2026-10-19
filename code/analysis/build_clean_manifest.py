"""Build manifest_clean.{jsonl,json} from manifest.jsonl and outputs/audit/broken_items.json.

The original manifest, specifications and configurations are left unchanged so that the
paper's tables and pinned revisions still reproduce. The clean manifest:
  - drops items whose action is "remove" (the reference does not parse);
  - lists items whose action is "demote_to_silver" as silver with no configuration
    (their configuration cannot be model-checked as released);
  - keeps "flag" items unchanged (they are listed in the audit for their dependency issue);
  - adds tla_path / cfg_path so a consumer need not infer locations from the tier.

Usage: python code/analysis/build_clean_manifest.py
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
broken = {item['spec_id']: item for item in json.loads((ROOT / 'outputs/audit/broken_items.json').read_text())}
rows = []
for line in (ROOT / 'manifest.jsonl').read_text().splitlines():
    rec = json.loads(line)
    sid = int(rec['spec_id'])
    item = broken.get(sid)
    if item and item['action'] == 'remove':
        continue
    tla = next((ROOT / 'specs' / rec['tier']).glob(f'{sid}_*.tla'))
    cfg = tla.with_suffix('.cfg')
    rec['tla_path'] = str(tla.relative_to(ROOT))
    rec['cfg_path'] = str(cfg.relative_to(ROOT)) if rec['tier'] == 'gold' and cfg.exists() else None
    if item and item['action'] == 'demote_to_silver':
        rec['tier'], rec['cfg_path'] = 'silver', None
        rec['clean_note'] = 'demoted from gold: ' + item['reason']
    rows.append(rec)
(ROOT / 'manifest_clean.jsonl').write_text(''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in rows))
(ROOT / 'manifest_clean.json').write_text(json.dumps(rows, ensure_ascii=False, indent=1) + '\n')
gold = sum(r['tier'] == 'gold' for r in rows)
print(f'{len(rows)} specifications: {gold} gold, {len(rows) - gold} silver')
