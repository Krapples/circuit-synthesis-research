"""Independent finite checks for the additive gate-elimination weight (experiments/additive_sat_weight.py, handoff
2026-11-26) and the SAT_(12q+6) gadget.

1. A separately written weight recurrence (tuple truth tables, module quotient through a neutral cofactor) agrees
   with the reference on every nonzero function of 1..3 inputs, random 4..6-input functions and both gadgets.
2. Soundness spot checks against exact minima (these cannot prove the theorem; they can refute it):
   * w(f) - 1 <= C(f) for every nonzero 4-input function: exact4 decides C <= 4 or C >= 5, and larger bounds use
     exact C per NPN class (results/sat_gadget/npn4_exact_aig.json, 66 gadget classes; with --fill all 222 classes
     by the same Percy ladder into npn4_exact_aig_all.json); bounds >= 6 without an exact C are counted unchecked;
   * C(AND_j f_j) >= sum_j w(f_j) - 1 for products of up to three factors on disjoint inputs (total <= 6 inputs),
     decided by the exact <= 4-gate projection oracle (native preduce_check --exact4-stdin): a bound <= 4 must not
     exceed the exact cost, and a bound >= 5 must come with a proven exclusion.
3. The gadget truth tables and compositions with the decoder written from the Lean definitions
   (experiments/sat_encoding_bound_review.py): exhaustive q = 1, 2 and random q = 3..6; and the repository's
   induction_certificate (experiments/sat_gadget_exact.py) for all q.
"""
import argparse
import importlib.util
import json
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f'{name}.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ---- independent weight: truth table as a tuple of 0/1 over rows, row bit k = input k ----
def to_tuple(f, n):
    return tuple((f >> r) & 1 for r in range(1 << n))


def restrict(t, n, i, b):
    return tuple(t[(r & ((1 << i) - 1)) | (b << i) | ((r >> i) << (i + 1))] for r in range(1 << (n - 1)))


def essential(t, n, i):
    return restrict(t, n, i, 0) != restrict(t, n, i, 1)


def shrink(t, n):
    i = 0
    while i < n:
        if essential(t, n, i):
            i += 1
        else:
            t, n = restrict(t, n, i, 0), n - 1
    return t, n


def quotient(t, n, i, j, a, b):
    """g(y, others) with f = g([x_i=a] AND [x_j=b], others), or None. Others keep their order; y is the last input."""
    rest = [k for k in range(n) if k not in (i, j)]
    out = [0] * (1 << (n - 1))
    for s in range(1 << (n - 2)):
        base = sum(((s >> t_) & 1) << k for t_, k in enumerate(rest))
        rows = {(u, v): t[base | (u << i) | (v << j)] for u in (0, 1) for v in (0, 1)}
        zero = {rows[(u, v)] for (u, v) in rows if (u, v) != (a, b)}
        if len(zero) != 1:
            return None
        out[s] = zero.pop()
        out[s | (1 << (n - 2))] = rows[(a, b)]
    return tuple(out)


@lru_cache(None)
def w2(t, n):
    assert any(t), 'zero factor'
    t, n = shrink(t, n)
    if n <= 1:
        return n
    for b in (0, 1):
        for i in range(n):
            if not any(restrict(t, n, i, 1 - b)):
                return 1 + w2(restrict(t, n, i, b), n - 1)
    best = min(max(3 + w2(restrict(t, n, i, 1 - a), n - 1), 2 + w2(restrict(t, n, i, a), n - 1))
               for i in range(n) for a in (0, 1))
    for i, j in combinations(range(n), 2):
        for a, b in product((0, 1), repeat=2):
            g = quotient(t, n, i, j, a, b)
            if g is not None:
                best = min(best, 1 + w2(g, n - 1))
    return best


def weight2(f, n):
    return w2(to_tuple(f, n), n)


# ---- NP(N) orbits on 4 inputs ----
def transform(f, perm, neg, n=4):
    out = 0
    for r in range(1 << n):
        s = sum((((r >> perm[k]) & 1) ^ ((neg >> k) & 1)) << k for k in range(n))
        out |= ((f >> r) & 1) << s
    return out


def product_table(factors):
    """factors: list of (f, m); inputs laid out consecutively. Returns (table, n)."""
    n = sum(m for _, m in factors)
    t = 0
    for r in range(1 << n):
        v, off = 1, 0
        for f, m in factors:
            v &= (f >> ((r >> off) & ((1 << m) - 1))) & 1
            off += m
        t |= v << r
    return t, n


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--exact4-exe', type=Path, default=HERE.parent / 'native' / 'preduce_check.exe')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--fill', action='store_true', help='exact C for all 222 NPN classes (Percy) into npn4_exact_aig_all.json')
    ap.add_argument('--workers', type=int, default=10)
    ap.add_argument('--random', type=int, default=300, help='random functions per width 4..6 for check 1')
    ap.add_argument('--products', type=int, default=20000, help='random products for check 2 (plus exhaustive pairs)')
    a = ap.parse_args()
    rng = random.Random(a.seed)
    ref = load('additive_sat_weight')
    rev = load('sat_encoding_bound_review')
    gad = load('sat_gadget_exact')
    report = {}

    # 1. two recurrences
    n_cmp = 0
    for n in range(1, 4):
        for f in range(1, 1 << (1 << n)):
            assert ref.weight(f, n) == weight2(f, n), (n, hex(f))
            n_cmp += 1
    for n in range(4, 7):
        for _ in range(a.random):
            f = rng.getrandbits(1 << n) or 1
            assert ref.weight(f, n) == weight2(f, n), (n, hex(f))
            n_cmp += 1
    G7 = 0xedc4ed00edc400c4edc4000000c40000
    for f, n, w in ((0x9, 2, 4), (0xe8e4, 4, 6), (0xedc4, 4, 7), (G7, 7, 12)):
        assert ref.weight(f, n) == weight2(f, n) == w
        n_cmp += 1
    report['recurrence_agreement'] = n_cmp

    # 2a. w - 1 <= exact C on every nonzero 4-input function
    cache = json.loads((HERE.parent / 'results/sat_gadget/npn4_exact_aig.json').read_text())
    assert all(v['upper'] <= v['witness'] for v in cache.values())  # witness = cofactor-library size
    # exact C per NPN class (keys = cofactor-library representatives). The committed gadget cache has 66 classes;
    # --fill computes the rest with the same Percy ladder into a separate file. Otherwise exact4 decides C <= 4 / >= 5.
    lib = gad.Library(HERE.parent / 'results/cofactor_witness/npn4_witnesses.json')
    if a.fill:
        full_path = HERE.parent / 'results/sat_gadget/npn4_exact_aig_all.json'
        full = json.loads(full_path.read_text()) if full_path.exists() else dict(cache)
        need = sorted({lib.index[f][0] for f in range(1 << 16)} - {int(k, 16) for k in full})
        seconds, conflicts = gad.F.TIERS['extended']

        def exact(rep):
            w = lib.chain(rep)
            if w['size'] <= 1:  # constants and literals need 0 gates, other functions >= 1: the witness is exact
                return rep, {'upper': w['size'], 'open_budget': None, 'status': 'TRIVIAL', 'witness': w['size'],
                             'seconds': 0}
            r = gad.F.run(gad.F.PERCY, gad.MODE, f'gadget-{rep:04x}', 4, rep, 0xffff, 'cegar', seconds, conflicts,
                          start=1, upper_witness=w['spec'])
            return rep, {'upper': r['upper_bound'], 'open_budget': r['open_budget'], 'status': r['status'],
                         'witness': w['size'], 'seconds': round(r['wall_seconds'], 3)}

        with ThreadPoolExecutor(a.workers) as pool:
            for rep, rec in pool.map(exact, need):
                full[f'{rep:04x}'] = rec
        full_path.write_text(json.dumps(full, indent=0, sort_keys=True) + '\n')
        cache = full
    for v in cache.values():
        assert v['status'] in ('SAT', 'TRIVIAL') or v['upper'] is not None, v
    # a lower bound on C suffices: the exact value, or open_budget when the ladder timed out (all smaller UNSAT)
    lower = lambda v: v['upper'] if v['open_budget'] is None else v['open_budget']
    seen = {f: (lower(cache[k]) if (k := f'{lib.index[f][0]:04x}') in cache else None) for f in range(1 << 16)}
    fs = list(range(1, 1 << 16))
    p = subprocess.run([str(a.exact4_exe), '--exact4-stdin'], capture_output=True, text=True,
                       input=''.join(f'4 {f:x} ffff\n' for f in fs))
    if p.returncode:
        raise RuntimeError(p.stderr)
    e4 = [json.loads(l) for l in p.stdout.splitlines()]
    assert len(e4) == len(fs)
    worst, tight, by_exact4, by_cache, unchecked = -99, 0, 0, 0, 0
    for f, r in zip(fs, e4):
        w = ref.weight(f, 4)
        c = seen[f]
        if r is not None:
            assert r['ok'] and (c is None or c <= r['cost']), (hex(f), r, c)
            c = r['cost']
        if c is not None:
            assert w - 1 <= c, (hex(f), w, c)
            worst, tight = max(worst, w - 1 - c), tight + (w - 1 == c)
            by_exact4 += r is not None
            by_cache += r is None
        elif w - 1 <= 5:  # exact4 exclusion proves C >= 5 >= w - 1
            by_exact4 += 1
        else:
            unchecked += 1
    report['four_input'] = dict(functions=len(fs), exact4_decided=by_exact4, sat_cache=by_cache,
                                unchecked_bound_ge6=unchecked, tight=tight, max_gap=worst)

    # 2b. products against the exact <= 4 oracle
    ess = {m: [f for f in range(1, (1 << (1 << m)) - 1) if all(essential(to_tuple(f, m), m, i) for i in range(m))]
           for m in range(1, 5)}
    ess[5] = None
    prods = []
    for m1 in range(1, 5):
        for m2 in range(m1, 6 - m1):
            for f in ess[m1]:
                for g in ess[m2]:
                    prods.append([(f, m1), (g, m2)])
    for _ in range(a.products):
        k = rng.choice((2, 3))
        ms = [rng.randint(1, 4) for _ in range(k)]
        while sum(ms) > 6:
            ms = [rng.randint(1, 4) for _ in range(k)]
        prods.append([(rng.choice(ess[m]), m) for m in ms])
    queries = []
    for fs in prods:
        t, n = product_table(fs)
        bound = sum(ref.weight(f, m) for f, m in fs) - 1
        queries.append((t, n, bound))
    full = lambda n: (1 << (1 << n)) - 1
    p = subprocess.run([str(a.exact4_exe), '--exact4-stdin'], capture_output=True, text=True,
                       input=''.join(f'{n} {t:x} {full(n):x}\n' for t, n, _ in queries))
    if p.returncode:
        raise RuntimeError(p.stderr)
    out = [json.loads(l) for l in p.stdout.splitlines()]
    assert len(out) == len(queries)
    tight = excl = hits = 0
    for (t, n, bound), r in zip(queries, out):
        if r is None:
            excl += 1
            continue
        assert r['ok']
        hits += 1
        assert r['cost'] >= bound, (n, hex(t), bound, r)
        tight += r['cost'] == bound
    # every product whose bound is >= 5 was excluded (otherwise the assert above failed)
    report['products'] = dict(queries=len(queries), exact_hits=hits, tight_hits=tight, excluded=excl)

    # 3. grammar
    def block_tt(template, m):
        names = [chr(97 + i) for i in range(m)]
        return sum(rev.sat(rev.fill(template, r, names) + '110100') << r for r in range(1 << m))

    comp = 0
    for template, m, f in (('11a1bcd1', 4, 0xedc4), ('11a1bcd1efg1', 7, G7)):
        names = [chr(97 + i) for i in range(m)]
        assert block_tt(template, m) == f
        assert all(any(((f >> r) & 1) != ((f >> (r ^ (1 << i))) & 1) for r in range(1 << m)) for i in range(m))
        assert gad.induction_certificate(template, '110100', m, f) is None
        for q in (1, 2):
            for zs in product(range(1 << m), repeat=q):
                s = ''.join(rev.fill(template, z, names) for z in zs) + '110100'
                assert rev.sat(s) == all((f >> z) & 1 for z in zs)
                comp += 1
        acc = [z for z in range(1 << m) if (f >> z) & 1]
        rej = [z for z in range(1 << m) if not (f >> z) & 1]
        for _ in range(2000):
            q = rng.randint(3, 6)
            zs = [rng.choice(acc) for _ in range(q)]
            if rng.random() < .5:
                zs[rng.randrange(q)] = rng.choice(rej)
            s = ''.join(rev.fill(template, z, names) for z in zs) + '110100'
            assert rev.sat(s) == all((f >> z) & 1 for z in zs)
            comp += 1
    report['composition_checks'] = comp
    # 4. arithmetic: n = 12q+6, m = 7q, B >= n - m + 12q - 1 = 17q + 5 > floor(4n/3) - 3 = 16q + 5
    for q in range(1, 2001):
        n = 12 * q + 6
        assert n - 7 * q + 12 * q - 1 == 17 * q + 5 > (4 * n) // 3 - 3 == 16 * q + 5
    report['ok'] = True
    print(json.dumps(report))


if __name__ == '__main__':
    sys.exit(main())
