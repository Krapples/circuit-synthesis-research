"""Compare tree_dp jsonl (min_k or gt) with native SAT minima (template_synth jsonl: status SAT, k)."""
import json, sys
nat = {d['id']: d for d in map(json.loads, open(sys.argv[1]))}
ok = bad = skip = 0
for d in map(json.loads, open(sys.argv[2])):
    if d.get('status') == 'skip': skip += 1; continue
    n = nat.get(d['id'])
    if n is None or n['status'] != 'SAT': continue
    good = (d['min_k'] == n['k']) if d['min_k'] is not None else (n['k'] > d['gt'])
    ok += good; bad += not good
    if not good: print('MISMATCH', d, n['k'])
print(f'agree {ok} disagree {bad} skip {skip}')
