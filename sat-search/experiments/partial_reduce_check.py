"""Differential check of native/preduce_check.exe (src/partial_reduce.hpp) against the handoff's Python reference.

Generates random and planted partial queries on 4..8 inputs, runs the reference greedy() / canonical() from a
reference module (--reference DIR containing reduce.py), and compares the core width, core table, step kinds and
inputs, offset and canonical core key with the native output. The native lifted Shannon chain must agree with the
original care set (lift_ok) and canonical keys must round-trip.

Planted queries: the truth table of a random small AIG (2..2n gates over n inputs) under a random care mask, which
exercises peel / module / zero rules far more often than uniform random tables.
"""
import argparse
import importlib.util
import json
import random
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXE = HERE.parent / 'native' / 'preduce_check.exe'


def planted(n, rng):
    cols = [sum(1 << r for r in range(1 << n) if r >> i & 1) for i in range(n)]
    full = (1 << (1 << n)) - 1
    for _ in range(rng.randint(2, 2 * n)):
        a, b = rng.sample(range(len(cols)), 2)
        cols.append((cols[a] ^ (full if rng.random() < .5 else 0)) & (cols[b] ^ (full if rng.random() < .5 else 0)))
    return cols[-1] ^ (full if rng.random() < .5 else 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--reference', type=Path, required=True)
    ap.add_argument('--count', type=int, default=500, help='queries per width and kind')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--exe', type=Path, default=EXE)
    a = ap.parse_args()
    spec = importlib.util.spec_from_file_location('reduce_ref', a.reference / 'reduce.py')
    ref = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ref)
    rng = random.Random(a.seed)
    qs = []
    for n in range(4, 9):
        full = (1 << (1 << n)) - 1
        for kind in ('random', 'planted'):
            for _ in range(a.count):
                dens = rng.choice((1.0, 1.0, .75, .5, .25))
                c = sum(1 << r for r in range(1 << n) if rng.random() < dens) or 1
                t = rng.getrandbits(1 << n) if kind == 'random' else planted(n, rng)
                qs.append((n, kind, t & c, c))
    hexd = lambda t, n: format(t, 'x')
    p = subprocess.run([str(a.exe), '--stdin'], input=''.join(f'{n} {hexd(t, n)} {hexd(c, n)}\n' for n, _, t, c in qs),
                       capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(p.stderr)
    out = [json.loads(l) for l in p.stdout.splitlines()]
    assert len(out) == len(qs)
    stats = {}
    mismatch = 0
    for (n, kind, t, c), r in zip(qs, out):
        m, q, d, steps = ref.greedy(t, c, n)
        s = stats.setdefault(f'{n}-{kind}', dict(queries=0, reduced=0, removed=0, mismatch=0))
        s['queries'] += 1
        s['reduced'] += bool(steps)
        s['removed'] += len(steps)
        ok = (r['core_n'] == m and int(r['core_p'], 16) == q and int(r['core_c'], 16) == d and
              r['offset'] == sum(x[4] for x in steps) and [tuple(x) for x in r['steps']] == [(x[0], x[1]) for x in steps]
              and r['lift_ok'])
        if m > 0 and q not in (0, d):
            (cq, cd), *_ = ref.canonical(q, d, m)
            ok = ok and int(r['canon_q'], 16) == cq and int(r['canon_d'], 16) == cd and r['canon_rt']
        if not ok:
            mismatch += 1
            s['mismatch'] += 1
            if mismatch <= 5:
                print('MISMATCH', n, kind, hex(t), hex(c), r, (m, hex(q), hex(d), [(x[0], x[1]) for x in steps]))
    print(json.dumps(dict(queries=len(qs), mismatch=mismatch, by=stats), indent=1))
    return 1 if mismatch else 0


if __name__ == '__main__':
    sys.exit(main())
