"""Import external four-input AIG witnesses (cofactor two-signal construction) as verified upper bounds.

Library format (results/cofactor_witness/npn4_witnesses.json, from ChatGPT's cofactor_witness_native bundle): one
record per NPN class representative, {'target', 'gates': [[a, b], ...], 'output'}; literal 2*w+p is wire w
complemented when p, wire 0 is constant zero, wires 1..4 the inputs x0..x3 (row r has x_i = bit i of r), wire 5+j
gate j = AND of its two literals.

For an arbitrary target f the importer finds a representative r and a transform with
f(x) = r(y) ^ o, y_j = x_{perm[j]} ^ m_j, rewrites the chain (input literal 2(j+1)+q -> 2(perm[j]+1) + (q ^ m_j),
output ^ o) and simulates it on all 16 rows. Every returned chain has been simulated against f; the witness is an
upper bound only. It is not a pinned prefix and does not follow Percy's canonical ordering.

Usage:
  python witness_import.py LIBRARY TT...      print the imported chain and its percy_run --upper-witness spec
  python witness_import.py LIBRARY --all      import and verify all 65,536 four-input functions
"""
import argparse
from itertools import permutations
import json
from pathlib import Path

N = 4
ROWS = 1 << N
FULL = (1 << ROWS) - 1


def simulate(gates, output):
    """Truth table of an indexed chain (independent row-by-row evaluation)."""
    tt = 0
    for r in range(ROWS):
        v = [0] + [(r >> i) & 1 for i in range(N)]
        for a, b in gates:
            if a // 2 >= len(v) or b // 2 >= len(v):
                raise ValueError('forward reference')
            v.append((v[a // 2] ^ (a & 1)) & (v[b // 2] ^ (b & 1)))
        if output // 2 >= len(v):
            raise ValueError('bad output')
        tt |= (v[output // 2] ^ (output & 1)) << r
    return tt


def transform_table(r, perm, mask, o):
    f = 0
    for x in range(ROWS):
        y = sum((((x >> perm[j]) & 1) ^ ((mask >> j) & 1)) << j for j in range(N))
        f |= (((r >> y) & 1) ^ o) << x
    return f


def transform_chain(gates, output, perm, mask, o):
    def lit(l):
        w, q = divmod(l, 2)
        if 1 <= w <= N:
            j = w - 1
            return 2 * (perm[j] + 1) + (q ^ ((mask >> j) & 1))
        return l
    return [[lit(a), lit(b)] for a, b in gates], lit(output) ^ o


class Library:
    def __init__(self, path):
        self.reps = {int(r['target'], 16): (r['gates'], r['output']) for r in json.loads(Path(path).read_text())}
        for rep, (gates, output) in self.reps.items():
            if simulate(gates, output) != rep:
                raise ValueError(f'library witness for {rep:04x} is wrong')
        self.index = {}
        for rep in self.reps:
            for perm in permutations(range(N)):
                for mask in range(ROWS):
                    for o in (0, 1):
                        self.index.setdefault(transform_table(rep, perm, mask, o), (rep, perm, mask, o))
        if len(self.index) != 1 << ROWS:
            raise ValueError(f'library covers {len(self.index)} of {1 << ROWS} functions')

    def chain(self, f):
        rep, perm, mask, o = self.index[f]
        gates, output = transform_chain(*self.reps[rep], perm, mask, o)
        if simulate(gates, output) != f:
            raise AssertionError(f'transformed witness for {f:04x} is wrong')
        return {'target': f'{f:04x}', 'rep': f'{rep:04x}', 'perm': list(perm), 'mask': mask, 'out_neg': o,
                'size': len(gates), 'gates': gates, 'output': output, 'spec': spec(gates, output)}


def spec(gates, output):
    return ';'.join(f'{a},{b}' for a, b in gates) + f'|{output}'


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('library', type=Path)
    p.add_argument('targets', nargs='*')
    p.add_argument('--all', action='store_true')
    a = p.parse_args()
    lib = Library(a.library)
    if a.all:
        sizes = [lib.chain(f)['size'] for f in range(1 << ROWS)]
        print(json.dumps({'representatives': len(lib.reps), 'functions_verified': len(sizes),
                          'max_size': max(sizes), 'total_size': sum(sizes)}))
    for t in a.targets:
        print(json.dumps(lib.chain(int(t, 16))))


if __name__ == '__main__':
    main()
