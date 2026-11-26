"""Differential check of native exact4 (src/exact4.hpp, via preduce_check.exe --exact4-stdin) against the handoff's
Python reference exact4 (--reference DIR containing projection.py).

Queries on 4..8 inputs: uniform random tables, planted random AIGs (2..2n gates), and small planted AIGs (1..4 gates
over a random support of at most 5 inputs, so exact hits and 5-input read-once cases occur), each under a random care
mask. Compares the decision (cost or exclusion), the chosen support and the complete small column; the native chain,
imported over the chosen inputs, must agree with the care set (ok).
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


def aig_column(n, rng, gates, inputs):
    full = (1 << (1 << n)) - 1
    cols = [sum(1 << r for r in range(1 << n) if r >> i & 1) for i in inputs]
    for _ in range(gates):
        a, b = rng.sample(range(len(cols)), 2)
        cols.append((cols[a] ^ (full if rng.random() < .5 else 0)) & (cols[b] ^ (full if rng.random() < .5 else 0)))
    return cols[-1] ^ (full if rng.random() < .5 else 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--reference', type=Path, required=True)
    ap.add_argument('--count', type=int, default=200, help='queries per width and kind')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--exe', type=Path, default=EXE)
    a = ap.parse_args()
    spec = importlib.util.spec_from_file_location('projection_ref', a.reference / 'projection.py')
    ref = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ref)
    rng = random.Random(a.seed)
    qs = []
    for n in range(4, 9):
        for kind in ('random', 'planted', 'small'):
            for _ in range(a.count):
                dens = rng.choice((1.0, .75, .5, .25, .1))
                c = sum(1 << r for r in range(1 << n) if rng.random() < dens) or 1
                if kind == 'random':
                    t = rng.getrandbits(1 << n)
                elif kind == 'planted':
                    t = aig_column(n, rng, rng.randint(2, 2 * n), range(n))
                else:
                    t = aig_column(n, rng, rng.randint(1, 4), sorted(rng.sample(range(n), rng.randint(2, min(5, n)))))
                qs.append((n, kind, t & c, c))
    p = subprocess.run([str(a.exe), '--exact4-stdin'],
                       input=''.join(f'{n} {t:x} {c:x}\n' for n, _, t, c in qs), capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(p.stderr)
    out = [json.loads(l) for l in p.stdout.splitlines()]
    assert len(out) == len(qs)
    stats = {}
    mismatch = 0
    for (n, kind, t, c), r in zip(qs, out):
        e = ref.exact4(t, c, n)
        s = stats.setdefault(f'{n}-{kind}', dict(queries=0, hits=0, excluded=0, cost=[0] * 5, mismatch=0))
        s['queries'] += 1
        if e is None:
            s['excluded'] += 1
            ok = r is None
        else:
            s['hits'] += 1
            s['cost'][e[0]] += 1
            ok = r is not None and r['cost'] == e[0] and tuple(r['vars']) == tuple(e[1]) and r['t'] == e[2] and r['ok']
        if not ok:
            mismatch += 1
            s['mismatch'] += 1
            if mismatch <= 5:
                print('MISMATCH', n, kind, hex(t), hex(c), r, e and e[:3])
    print(json.dumps(dict(queries=len(qs), mismatch=mismatch, by=stats), indent=1))
    return 1 if mismatch else 0


if __name__ == '__main__':
    sys.exit(main())
