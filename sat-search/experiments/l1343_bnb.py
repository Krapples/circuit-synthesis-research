"""Validation of bnb.py on the 23 L-meta-1343 shard-2 size-19 survivors (results/l1343_size19_survivors.json).
Each survivor's pinned prefix is a root (case a: 4 gates, colex from gate 3, size 19; case b: 3 gates, colex
from gate 2, size 18 -- as in l1343_full.tasks_for); its children are closed analytically where possible
and the rest go to conflict-limited SAT. One resumable tree per survivor in results/bnb_l1343/.
Usage: python experiments/l1343_bnb.py [workers] [sat_seconds] [survivor_id ...]"""
import json, os, subprocess, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE)
import l1343_full as L

if __name__ == '__main__':
    workers = sys.argv[1] if len(sys.argv) > 1 else '4'
    secs = sys.argv[2] if len(sys.argv) > 2 else '1800'
    only = set(sys.argv[3:])
    S = json.load(open(os.path.join(HERE, 'results', 'l1343_size19_survivors.json')))
    os.makedirs(os.path.join(HERE, 'results', 'bnb_l1343'), exist_ok=True)
    edges = ','.join(f'{u}-{v}' for u, v in L.EDGES)
    # case b first (fewer pinned gates, cheaper bounds), then case a
    for s in sorted(S['survivors'], key=lambda s: (s['case'] != 'b', s['id'])):
        if only and s['id'] not in only:
            continue
        tree = os.path.join(HERE, 'results', 'bnb_l1343', s['id'].replace(':', '_') + '.jsonl')
        seed = ';'.join(','.join(map(str, g)) for g in s['prefix'])
        t0 = time.time()
        out = subprocess.run([sys.executable, os.path.join(HERE, 'bnb.py'), '--n', str(L.n), '--edges', edges,
                              '--size', str(s['budget']), '--seed-prefix', seed, '--colex-from', str(s['colex_from']),
                              '--root-children', '--workers', workers, '--sat-seconds', secs, '--tree', tree],
                             capture_output=True, text=True, cwd=HERE).stdout
        result = [l for l in out.splitlines() if l.startswith('RESULT') or l.startswith('WITNESS')]
        print(f'{s["id"]}: {result[-1] if result else out[-300:]} ({time.time() - t0:.0f}s)', flush=True)
