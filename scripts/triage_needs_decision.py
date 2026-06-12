import json, sys, re, tempfile
from pathlib import Path
from collections import Counter
sys.path.insert(0,'scripts'); sys.path.insert(0,'src')
import roundtrip_fidelity as F, review_triage as RT

mdir=Path('data/dataset_manifest')
logdir=mdir/'tlc_logs'; logdir.mkdir(exist_ok=True)
nd=json.load(open(mdir/'needs_decision.json'))
rows=[]
for r in nd:
    tla=F.REPO_ROOT/r['tla_path']
    with tempfile.TemporaryDirectory() as t:
        wd=Path(t); mt=tla.read_text(errors='replace')
        F._copy_siblings(tla.parent, wd); F.copy_dependencies(mt, tla.parent, wd)
        cfg=RT.find_valid_cfg(tla.stem, tla.parent, wd, mt)
        if not cfg:
            outcome='no_valid_cfg'; firsterr=''
        else:
            res=RT.run_tlc_nodeadlock(wd/tla.name, cfg, 30)
            (logdir/f"{r['spec_id']}_{tla.stem}.log").write_text(res['out']+'\n--ERR--\n'+res['err'])
            outcome=RT.classify(res)
            errs=[l for l in res['out'].splitlines() if l.startswith('Error:')]
            firsterr=errs[0][:120] if errs else ''
    # finer disposition
    blob=firsterr.lower()
    if outcome=='pass': disp='RECOVER_gold'
    elif outcome=='no_valid_cfg': disp='SILVER_no_cfg'
    elif 'assumption' in blob: disp='ASSUMPTION (smoke/missing-const)'
    elif 'parsing' in blob or 'cannot find' in blob or 'unknown operator' in blob: disp='STAGING/PARSE'
    elif 'unexpected exception' in blob or 'java.lang' in blob: disp='DROP_runtime'
    elif 'not assigned' in blob or 'undefined identifier' in blob or 'substitut' in blob: disp='CONFIG'
    else: disp='OTHER'
    rows.append({**r,'retest_outcome':outcome,'first_error':firsterr,'disposition':disp})
json.dump(rows, open(mdir/'needs_decision_triaged.json','w'), indent=2)
print('=== 52 needs_decision retriaged ===')
for d,n in Counter(x['disposition'] for x in rows).most_common(): print(f'  {n:3d}  {d}')
print()
print('sample errors by disposition:')
seen=set()
for x in rows:
    if x['disposition'] in seen: continue
    seen.add(x['disposition'])
    print(f"  [{x['disposition']}] {Path(x['tla_path']).name}: {x['first_error'][:90]}")
