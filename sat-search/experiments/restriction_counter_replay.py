"""Pruning coverage of eager restriction counters on captured Percy CEGAR models.

For each captured model (restriction_capture.py output) and budget k, a counter for restriction pi
excludes the model when its deletion count exceeds k - L(f o pi). Configurations:
- zero4: constant-only counters for x_i := 0 (zero-anchored, one flag per wire);
- const8: constant-only counters for x_i := 0 and x_i := 1;
- anchor4: per primary, the constant value with the larger restricted cost (ties favour 0); this is
  what input-complement re-normalization puts at zero, evaluated here in the original coordinates
  (constant deletions are invariant under complementing an input);
- ids20: representative-ID (alias) counters on all 20 restrictions, without structural hashing;
- ids_zero10: representative-ID counters on the 10 restrictions that contain row zero;
- cert20: the earlier certificate rule (alias closure with structural hashing, all 20).
Constant-only deletions are recomputed here by direct propagation (gates with a provably constant
operand), independently of the native CNF encoding.
"""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path

from restriction_replay import OPS, restrictions, structural


def constant_deletions(n, init, gates):
    value = [entry[1] if entry[0] == 'const' else None for entry in init]
    deleted = 0
    for a, b, pa, pb, inv in gates:
        x, y = value[a], value[b]
        x = None if x is None else x ^ (1 - pa)
        y = None if y is None else y ^ (1 - pb)
        deleted += x is not None or y is not None
        z = 0 if x == 0 or y == 0 else (1 if x == 1 and y == 1 else None)
        value.append(None if z is None else z ^ inv)
    return deleted


def alias_deletions(n, init, gates, hashing):
    if hashing:
        return len(structural(n, init, gates))
    lit = [('c', e[1]) if e[0] == 'const' else ('w', e[1], e[2]) for e in init]
    neg = lambda x, f: x if not f else (('c', 1 - x[1]) if x[0] == 'c' else ('w', x[1], 1 - x[2]))
    deleted = 0
    for t, (a, b, pa, pb, inv) in enumerate(gates):
        x, y = neg(lit[a], not pa), neg(lit[b], not pb)
        if x == ('c', 0) or y == ('c', 0):
            z = ('c', 0)
        elif x == ('c', 1):
            z = y
        elif y == ('c', 1):
            z = x
        elif x == y:
            z = x
        elif x == neg(y, True):
            z = ('c', 0)
        else:
            lit.append(('w', n + t, inv))
            continue
        deleted += 1
        lit.append(neg(z, inv))
    return deleted


def coverage(job):
    path, target, k, cost3 = job
    rs = restrictions(4, int(target, 16), cost3)
    # rs order: x0=0, x0=1, x1=0, ..., then identifications (j, i, b) with b alternating.
    const = list(range(8))
    zero4 = [0, 2, 4, 6]
    anchor4 = [2 * i + (rs[2 * i + 1][2] > rs[2 * i][2]) for i in range(4)]
    zero10 = zero4 + [j for j in range(8, 20) if j % 2 == 0]
    stats = Counter()
    for line in path.read_text().splitlines():
        gates = [(a, b, *OPS[op]) for op, a, b in json.loads(line)['chain']]
        stats['models'] += 1
        cdel = {j: constant_deletions(4, rs[j][1], gates) for j in const}
        cut = lambda j, d: d > k - rs[j][2]
        flags = {
            'zero4': any(cut(j, cdel[j]) for j in zero4),
            'const8': any(cut(j, cdel[j]) for j in const),
            'anchor4': any(cut(j, cdel[j]) for j in anchor4),
        }
        ids = {j: alias_deletions(4, rs[j][1], gates, False) for j in range(20)}
        flags['ids_zero10'] = any(cut(j, ids[j]) for j in zero10)
        flags['ids20'] = any(cut(j, ids[j]) for j in range(20))
        flags['cert20'] = any(cut(j, alias_deletions(4, rs[j][1], gates, True)) for j in range(20))
        for j in const:
            assert cdel[j] <= ids[j], (target, k, j)  # constants are a sub-abstraction of IDs
        for name, hit in flags.items():
            stats[name] += hit
        stats['const8_not_cert'] += flags['const8'] and not flags['cert20']
    return target, k, path.name.split('_')[0], dict(stats), anchor4


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('costs3', type=Path)
    parser.add_argument('--workers', type=int, default=11)
    args = parser.parse_args()
    cost3 = json.loads(args.costs3.read_text())
    jobs = []
    for path in sorted(args.capture.glob('*.models.jsonl'), key=lambda p: -p.stat().st_size):
        mode, target, k = path.name.split('.')[0].split('_')
        jobs.append((path, target, int(k), cost3))
    totals = Counter()
    with ProcessPoolExecutor(args.workers) as pool:
        for target, k, mode, stats, anchor in pool.map(coverage, jobs):
            print(json.dumps({'mode': mode, 'target': target, 'k': k, 'anchor4': anchor, **stats}), flush=True)
            totals.update({f'{mode}_k{k}_{key}': v for key, v in stats.items()})
            totals.update({f'all_{key}': v for key, v in stats.items()})
    print(json.dumps(dict(sorted(totals.items()))))


if __name__ == '__main__':
    main()
