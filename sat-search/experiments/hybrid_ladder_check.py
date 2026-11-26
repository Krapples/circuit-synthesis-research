"""Ladder check of --hybrid-witness: minima must match the control on targets with known minima.
W=1 forces every non-trivial budget through the skip / proof path."""
import sys, json
from concurrent.futures import ThreadPoolExecutor
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'baselines'))
import first_layer_check as F
base = F.RESIDUAL_MODES['slack-three-phase-set-lift1-count-const-liveall-ess']
F.RESIDUAL_MODES['hyb-w1'] = (*base, '--hybrid-witness', '1')
F.RESIDUAL_MODES['hyb-w1-slice'] = (*base, '--hybrid-witness', '1', '--restriction-cone-slice', '50')
F.RESIDUAL_MODES['hyb-w100'] = (*base, '--hybrid-witness', '100')
modes = ['slack-three-phase-set-lift1-count-const', 'hyb-w1', 'hyb-w1-slice', 'hyb-w100']
targets = [(3, t) for t in (0x80, 0xca, 0xe8, 0x96, 0x1b, 0x1e, 0x6a, 0x69)]
targets += [(4, t) for t in (0x8880, 0x6996, 0x0116, 0x016a, 0x1668, 0x0168, 0x01e8, 0x1ee1)]
jobs = [(m, n, t) for n, t in targets for m in modes]
def go(j):
    m, n, t = j
    r = F.run(F.PERCY, m, f'{t:x}', n, t, (1 << (1 << n)) - 1, 'cegar', 120, 0, start=1)
    return m, n, t, r['status'], r['upper_bound'], [(x['k'], x.get('phase'), x['status']) for x in r['records'] if 'k' in x]
res = {}
with ThreadPoolExecutor(10) as p:
    for m, n, t, st, ub, recs in p.map(go, jobs):
        res[(m, n, t)] = (st, ub)
        print(m, n, hex(t), st, ub, recs, flush=True)
bad = 0
for n, t in targets:
    ref = res[(modes[0], n, t)]
    for m in modes[1:]:
        if res[(m, n, t)] != ref: bad += 1; print('MISMATCH', m, n, hex(t), res[(m, n, t)], ref)
print('jobs', len(jobs), 'mismatches', bad)
