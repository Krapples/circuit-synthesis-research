"""Conditional restriction counters on captured Percy CEGAR models (independent replay).

Rule (free-NOT AIG, constant restriction x_i := b of a complete four-input target f):
- forward: U = k - D, where D counts the gates with a provably constant operand (constant propagation
  only). H is the set of one-gate functions of the three free inputs that are computed by first-layer gates
  (both operands primaries) on two unfixed primaries. Those gates never have a constant operand, so they
  survive the bypass, and the simplified circuit computes f o pi and every h in H. Hence
  U >= M(f o pi, H), the multi-output cost with free output phases.
- cone: U = number of binary gates of the restricted output cone, and H only the first-layer gates inside
  that cone.
Singleton clauses use max over h in H of M(f o pi, {h}), which is L or L + 1. 'all' uses the full
mask entry (a certified lower bound; 7 means >= 7).

The table is the bundle's first_layer_cost_table.bin (128 complement-normalized targets x 4096 masks of
the twelve one-gate functions, one byte each), reproduced byte for byte with MSVC. Its column order:
bit r of a three-input column is the value on row r, variable t is bit t of r, as in
restriction_replay.restrictions (rows enumerate the free inputs in increasing order).
"""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path

from restriction_counter_replay import constant_deletions, cone, essential
from restriction_replay import OPS, restrictions

ONE = (3, 5, 10, 12, 17, 34, 48, 63, 68, 80, 95, 119)
BIT = {x: 1 << i for i, x in enumerate(ONE)}


def load_table(path):
    data = Path(path).read_bytes()
    assert len(data) == 128 * 4096
    return data


def lb(table, f, mask):
    return table[min(f, 255 ^ f) * 4096 + mask]


def wire_values(n, gates):
    mask = (1 << (1 << n)) - 1
    v = [sum(((r >> i) & 1) << r for r in range(1 << n)) for i in range(n)]
    for a, b, pa, pb, inv in gates:
        x = v[a] if pa else v[a] ^ mask
        y = v[b] if pb else v[b] ^ mask
        v.append((x & y) ^ (mask if inv else 0))
    return v


def project(col, rows):
    return sum(((col >> r) & 1) << s for s, r in enumerate(rows))


def first_layer_masks(n, gates, values, rows, fixed, live):
    """(forward mask, cone mask) of one-gate columns of first-layer gates on unfixed primaries."""
    fwd = cone_mask = 0
    for t, (a, b, *_rest) in enumerate(gates):
        if a >= n or b >= n or fixed in (a, b):
            continue
        h = project(values[n + t], rows)
        bit = BIT.get(min(h, 255 ^ h))
        assert bit, (gates, t, h)  # an AND of two signed free primaries is a one-gate function
        fwd |= bit
        if n + t in live:
            cone_mask |= bit
    return fwd, cone_mask


def live_set(n, init, gates):
    value = [e[1] if e[0] == 'const' else None for e in init]
    for a, b, pa, pb, inv in gates:
        x, y = value[a], value[b]
        x = None if x is None else x ^ (1 - pa)
        y = None if y is None else y ^ (1 - pb)
        z = 0 if x == 0 or y == 0 else (1 if x == 1 and y == 1 else None)
        value.append(None if z is None else z ^ inv)
    live = {n + len(gates) - 1}
    for t in range(len(gates) - 1, -1, -1):
        g = n + t
        if g not in live or value[g] is not None:
            continue
        live.update(w for w in gates[t][:2] if value[w] is None)
    return {g for g in live if g >= n and value[g] is None}


def singleton(table, f, mask):
    return max([lb(table, f, 0)] + [lb(table, f, 1 << i) for i in range(12) if mask >> i & 1])


def coverage(job):
    path, target, k, cost3, table_path = job
    table = load_table(table_path)
    tt = int(target, 16)
    rs = restrictions(4, tt, cost3)
    const = list(range(8))
    need = {j: essential(tt, 4, rs[j][3], j // 2) for j in const}
    stats = Counter()
    clause_count = 0
    for j in const:
        f3 = project(tt, rs[j][3])
        assert lb(table, f3, 0) == rs[j][2], (target, j)  # table agrees with aig_costs3
        clause_count += sum(lb(table, f3, 1 << i) > rs[j][2] for i in range(12))
    stats['singleton_clauses'] = clause_count
    for line in path.read_text().splitlines():
        gates = [(a, b, *OPS[op]) for op, a, b in json.loads(line)['chain']]
        assert len(gates) == k
        values = wire_values(4, gates)
        stats['models'] += 1
        hit = Counter()
        for j in const:
            name, init, L, rows = rs[j]
            f3 = project(tt, rows)
            fixed = j // 2
            d = constant_deletions(4, init, gates)
            u = k - d
            kept, reached = cone(4, init, gates)
            live = live_set(4, init, gates)
            assert len(live) >= kept
            fwd, cmask = first_layer_masks(4, gates, values, rows, fixed, live)
            hit['const8'] |= u < L
            hit['cond1'] |= u < singleton(table, f3, fwd)
            hit['condall'] |= u < lb(table, f3, fwd)
            hit['live8'] |= kept < L
            hit['ess8'] |= bool(need[j] - reached)
            hit['conecond1'] |= kept < singleton(table, f3, cmask)
            hit['coneall'] |= kept < lb(table, f3, cmask)
            # The cone variant must not reuse forward presence: show where that would be stronger (unsound).
            hit['cone_with_fwd_mask_UNSOUND'] |= kept < singleton(table, f3, fwd)
        stats.update({key: int(v) for key, v in hit.items()})
        survivor = not hit['const8']
        stats['const8_survivors'] += survivor
        for key in ('cond1', 'condall', 'live8', 'ess8', 'conecond1', 'coneall'):
            stats[f'{key}_beyond_const8'] += survivor and hit[key]
        cone_ess = hit['live8'] or hit['ess8']
        stats['live8_ess8_beyond_const8'] += survivor and cone_ess
        stats['cond1_live8_ess8_beyond_const8'] += survivor and (cone_ess or hit['cond1'])
        stats['all_cone_cond_beyond_const8'] += survivor and (cone_ess or hit['cond1'] or hit['conecond1'])
        stats['cond1_beyond_live8_ess8'] += survivor and hit['cond1'] and not cone_ess
        stats['conecond1_beyond_live8_ess8'] += survivor and hit['conecond1'] and not cone_ess
    return target, k, path.name.split('_')[0], dict(stats)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('costs3', type=Path)
    parser.add_argument('table', type=Path)
    parser.add_argument('--workers', type=int, default=11)
    args = parser.parse_args()
    cost3 = json.loads(args.costs3.read_text())
    jobs = []
    for path in sorted(args.capture.glob('*.models.jsonl'), key=lambda p: -p.stat().st_size):
        mode, target, k = path.name.split('.')[0].split('_')
        jobs.append((path, target, int(k), cost3, str(args.table)))
    totals = Counter()
    with ProcessPoolExecutor(args.workers) as pool:
        for target, k, mode, stats in pool.map(coverage, jobs):
            print(json.dumps({'mode': mode, 'target': target, 'k': k, **stats}), flush=True)
            totals.update({f'all_{key}': v for key, v in stats.items() if key != 'singleton_clauses'})
    print(json.dumps(dict(sorted(totals.items()))))


if __name__ == '__main__':
    main()
