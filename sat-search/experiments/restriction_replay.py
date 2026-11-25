"""Independent replay of captured Percy CEGAR models against restriction certificates.

For each model (a k-gate free-NOT AIG chain in Percy's normalized ops) and each constant or
(complementary) identification restriction pi of the four-input target:
- structural deletions: an independent re-implementation of constant/alias/equal-operand/structural
  hashing propagation with per-deletion proofs (pair-only for operator-independent deletions);
- semantic deletions: gates equal under pi to a constant or, up to complement, an earlier wire
  (an upper bound on what any local certificate can reach).
A model is rejected when some restriction has more than k - L(f o pi) deletions; L comes from the
exact three-input cost table. Each rejecting core is checked by resampling every step outside it
(and the phases of its pair-only steps) and confirming semantically that at least the required
number of deletions survives.

Reports rejection fractions, core widths, operator-independent (pair-only) steps, repeats and
subsumption among cores, per budget.
"""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path
import random

MASK = 0xFFFF
OPS = {8: (1, 1, 0), 2: (1, 0, 0), 4: (0, 1, 0), 14: (0, 0, 1)}  # op -> (pa, pb, inv)


def primaries(n):
    return [sum(((r >> i) & 1) << r for r in range(1 << n)) for i in range(n)]


def restrictions(n, tt, cost3):
    """(name, initial literal per input, lower bound, list of original rows kept)."""
    out = []
    others = lambda skip: [v for v in range(n) if v != skip]
    for i in range(n):
        for b in (0, 1):
            init = [('const', b) if j == i else ('var', j, 0) for j in range(n)]
            rows = []
            for s in range(1 << (n - 1)):
                r = b << i
                for t, v in enumerate(others(i)):
                    r |= ((s >> t) & 1) << v
                rows.append(r)
            out.append((f'x{i}={b}', init, rows))
    for i in range(n):
        for j in range(i + 1, n):
            for b in (0, 1):
                init = [('var', i, b) if k == j else ('var', k, 0) for k in range(n)]
                rows = []
                for s in range(1 << (n - 1)):
                    r = 0
                    for t, v in enumerate(others(j)):
                        r |= ((s >> t) & 1) << v
                    r |= (((r >> i) & 1) ^ b) << j
                    rows.append(r)
                out.append((f'x{j}={"~" if b else ""}x{i}', init, rows))
    result = []
    for name, init, rows in out:
        g = sum(((tt >> r) & 1) << s for s, r in enumerate(rows))
        result.append((name, init, cost3[g], rows))
    return result


def structural(n, init, gates):
    """Deletions with proofs (pairs, typed) as step bitmasks; literal keys: ('c',v) or ('w',idx,neg)."""
    lit = []
    for entry in init:
        lit.append(('c', entry[1]) if entry[0] == 'const' else ('w', entry[1], entry[2]))
    proof = [(0, 0)] * n
    table = {}
    events = []

    def neg(x, flip):
        if not flip:
            return x
        return ('c', 1 - x[1]) if x[0] == 'c' else ('w', x[1], 1 - x[2])

    def union(*ps):
        return (eval_or([p[0] for p in ps]), eval_or([p[1] for p in ps]))

    def eval_or(xs):
        v = 0
        for x in xs:
            v |= x
        return v

    for t, (a, b, pa, pb, inv) in enumerate(gates):
        x, y = neg(lit[a], not pa), neg(lit[b], not pb)
        p, q = proof[a], proof[b]
        own, pair = (1 << t, 1 << t), (1 << t, 0)
        fresh = ('w', n + t, 0)
        if x == ('c', 0) or y == ('c', 0):
            options = []
            if x == ('c', 0):
                options.append(union(own, p))
            if y == ('c', 0):
                options.append(union(own, q))
            z, why = ('c', 0), min(options, key=lambda r: bin(r[0]).count('1') + bin(r[1]).count('1'))
        elif x == ('c', 1):
            z, why = y, union(own, p, q)
        elif y == ('c', 1):
            z, why = x, union(own, p, q)
        elif x == y:
            z, why = x, union(own, p, q)
        elif x == neg(y, True):
            z, why = ('c', 0), union(own, p, q)
        else:
            key = tuple(sorted((x, y)))
            if key in table:
                first, first_proof = table[key]
                z, why = first, union(own, p, q, first_proof)
            else:
                table[key] = (neg(fresh, inv), union(own, p, q))
                z, why = neg(fresh, inv), (0, 0)
        z = neg(z, inv)
        if z != fresh:
            if x[0] == 'c' or y[0] == 'c':
                options = []
                if x[0] == 'c':
                    options.append(union(pair, p))
                if y[0] == 'c':
                    options.append(union(pair, q))
                deletion = min(options, key=lambda r: bin(r[0]).count('1') + bin(r[1]).count('1'))
            elif x == y or x == neg(y, True):
                deletion = union(pair, p, q)
            else:
                deletion = why
            events.append((t, deletion))
        lit.append(z)
        proof.append(why)
    return events


def evaluate(n, init, gates):
    base = primaries(n)
    wires = []
    for entry in init:
        wires.append((MASK if entry[1] else 0) if entry[0] == 'const' else base[entry[1]] ^ (MASK if entry[2] else 0))
    for a, b, pa, pb, inv in gates:
        wires.append(((wires[a] ^ (0 if pa else MASK)) & (wires[b] ^ (0 if pb else MASK))) ^ (MASK if inv else 0))
    return wires


def semantic(n, init, gates):
    wires = evaluate(n, init, gates)
    out = []
    for t in range(len(gates)):
        w = wires[n + t]
        if w in (0, MASK) or any(w in (u, u ^ MASK) for u in wires[:n + t]):
            out.append(t)
    return out


def covers(core, proof):
    return proof[0] & ~core[0] == 0 and proof[1] & ~core[1] == 0


def cost(core):
    return bin(core[0]).count('1') + bin(core[1]).count('1')


def greedy_core(events, need):
    core = (0, 0)
    while sum(covers(core, p) for _, p in events) < need:
        core = min(((core[0] | p[0], core[1] | p[1]) for _, p in events if not covers(core, p)), key=cost)
    for i in range(64):
        bit = 1 << i
        if core[1] & bit and sum(covers((core[0], core[1] ^ bit), p) for _, p in events) >= need:
            core = (core[0], core[1] ^ bit)
    for i in range(64):
        bit = 1 << i
        if core[0] & bit and not core[1] & bit and \
                sum(covers((core[0] ^ bit, core[1]), p) for _, p in events) >= need:
            core = (core[0] ^ bit, core[1])
    return core


def mutate(rng, n, gates, core):
    out = []
    for t, gate in enumerate(gates):
        bit = 1 << t
        if core[1] & bit:
            out.append(gate)
            continue
        if core[0] & bit:
            a, b = gate[0], gate[1]
        else:
            a, b = sorted(rng.sample(range(n + t), 2))
        pa, pb, inv = OPS[rng.choice(list(OPS))]
        out.append((a, b, pa, pb, inv))
    return out


def replay(job):
    record, capture, cost3, mutations, seed = job
    mode, target, k = record['mode'], record['target'], record['k']
    rng = random.Random(f'{seed}-{mode}-{target}-{k}')
    path = capture / f'{mode}_{target}_{k}.models.jsonl'
    rs = restrictions(4, int(target, 16), cost3)
    stats = Counter()
    widths = Counter()
    cores = set()
    for line in path.read_text().splitlines():
        model = json.loads(line)
        gates = [(a, b, *OPS[op]) for op, a, b in model['chain']]
        stats['models'] += 1
        best = None
        semantic_reject = False
        for name, init, lower, _ in rs:
            allow = k - lower
            if allow < 0:
                best = ((0, 0), name, 0)
                semantic_reject = True
                break
            sem = semantic(4, init, gates)
            semantic_reject |= len(sem) > allow
            events = structural(4, init, gates)
            assert {t for t, _ in events} <= set(sem), (target, k, name, model)
            if len(events) <= allow:
                continue
            core = greedy_core(events, allow + 1)
            for _ in range(mutations):
                other = mutate(rng, 4, gates, core)
                assert len(semantic(4, init, other)) >= allow + 1, (target, k, name, core, model, other)
                stats['mutations'] += 1
            literals = bin(core[0]).count('1') + 2 * bin(core[1]).count('1')
            if best is None or literals < best[2]:
                best = (core, name, literals)
        stats['semantic_rejects'] += semantic_reject
        if best is None:
            continue
        core = best[0]
        stats['rejects'] += 1
        stats['empty'] += core == (0, 0)
        stats['literals'] += best[2]
        stats['pair_only'] += bin(core[0] & ~core[1]).count('1')
        stats['typed'] += bin(core[1]).count('1')
        widths[min(best[2], 16)] += 1
        key = (core, tuple(tuple(model['chain'][t]) for t in range(k) if core[0] >> t & 1))
        stats['repeats'] += key in cores
        cores.add(key)
    assert stats['models'] == record['restriction_models'], (target, k)
    assert stats['rejects'] == record['restriction_rejects'], (target, k, dict(stats), record['restriction_rejects'])
    return {'mode': mode, 'target': target, 'k': k, 'status': record['status'], 'reason': record['reason'],
            'rows': record['cegar_rows'], 'percy_literals': record['restriction_literals'], **stats,
            'widths': dict(sorted(widths.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path, help='directory written by restriction_capture.py')
    parser.add_argument('costs3', type=Path, help='JSON list of 256 exact three-input costs')
    parser.add_argument('--mutations', type=int, default=2)
    parser.add_argument('--seed', type=int, default=7)
    parser.add_argument('--workers', type=int, default=11)
    args = parser.parse_args()
    cost3 = json.loads(args.costs3.read_text())
    records = [json.loads(line) for line in (args.capture / 'records.jsonl').read_text().splitlines()]
    records.sort(key=lambda r: -r['restriction_models'])
    totals = Counter()
    with ProcessPoolExecutor(args.workers) as pool:
        for row in pool.map(replay, [(r, args.capture, cost3, args.mutations, args.seed) for r in records]):
            print(json.dumps(row), flush=True)
            totals.update({f"{row['mode']}_{key}": value for key, value in row.items()
                           if isinstance(value, int) and key != 'k'})
    print(json.dumps(dict(sorted(totals.items()))))


if __name__ == '__main__':
    main()
