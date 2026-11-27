"""Independent checks for mixed_rank_cuts.py (theorem regression, encoding exactness, corpus).

  1. Rank code vs a dense reference (truth-table matrix built separately, Gaussian elimination).
  2. Theorem regression: every AND/OR/NOT circuit on 4 inputs with <= G gates (exhaustive) and random
     circuits on 5-6 inputs: for every cut, mixed AND/OR gates in the cone >= floor(rank).
  3. Sharpness: the rank-one chain g_i = (g_{i-1} + a_i + b_i)(c_i + d_i) reaches 2^(t+1) - 2.
  4. Encoding exactness: pin cube_search.build selectors to a fixed circuit; the CNF with a cut of
     floor c is SAT iff the structural count is >= c (both the exact and the padded/cone form).
  5. Corpus: every complete synthesis case's witness satisfies all its cut floors.

Usage: python -B experiments/mixed_rank_cuts_check.py [--exhaustive-gates 4] [--random 20000]
"""
import argparse, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE)); sys.path.insert(1, HERE)
import cube_search as cs  # noqa: E402  (also puts .scratch-sat on the path)
from mixed_rank_cuts import (anchored_mixed_rank, cut_floors, mixed_floor, structural_mixed_counts,
                             add_mixed_rank_cuts)  # noqa: E402
from pysat.solvers import Solver  # noqa: E402


def dense_rank(n, truth, side):
    xs = [v for v in range(n) if side >> v & 1]; qs = [v for v in range(n) if not side >> v & 1]
    f = lambda r: truth >> r & 1
    def idx(vs, p): return sum(1 << v for k, v in enumerate(vs) if p >> k & 1)
    M = [[f(idx(xs, a) | idx(qs, b)) ^ f(idx(xs, a)) ^ f(idx(qs, b)) ^ f(0)
          for b in range(1 << len(qs))] for a in range(1 << len(xs))]
    rank, cols = 0, len(M[0]) if M else 0
    for c in range(cols):
        piv = next((r for r in range(rank, len(M)) if M[r][c]), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        for r in range(len(M)):
            if r != rank and M[r][c]:
                M[r] = [u ^ w for u, w in zip(M[r], M[rank])]
        rank += 1
    return rank


def table(n, gates):
    full = (1 << (1 << n)) - 1
    vals = [sum(1 << r for r in range(1 << n) if r >> v & 1) for v in range(n)]
    for op, a, b in gates:
        vals.append(vals[a] & vals[b] if op == 0 else vals[a] | vals[b] if op == 1 else full ^ vals[a])
    return vals


def check_circuit(n, gates, stats):
    vals = table(n, gates)
    out = n + len(gates) - 1
    t = vals[out]
    for side in range(1, (1 << n) - 1):
        if not side & 1:
            continue  # complementary cut has the same rank and count
        r = anchored_mixed_rank(n, t, side)
        c = structural_mixed_counts(n, gates, out, side)
        stats['cuts'] += 1
        if c < mixed_floor(r):
            raise AssertionError(f'violation n={n} gates={gates} side={side:b} rank={r} count={c}')
        if c == mixed_floor(r) and r:
            stats['tight'] += 1


def exhaustive(n, G, stats):
    def rec(gates):
        if gates:
            check_circuit(n, gates, stats); stats['circuits'] += 1
        if len(gates) == G:
            return
        w = n + len(gates)
        for a in range(w):
            rec(gates + [(2, a, a)])
            for b in range(a + 1, w):
                rec(gates + [(0, a, b)]); rec(gates + [(1, a, b)])
    rec([])


def random_circuits(count, rng, stats):
    for _ in range(count):
        n = rng.choice((5, 6)); G = rng.randint(3, 9); gates = []
        for j in range(G):
            w = n + j; op = rng.choice((0, 0, 1, 1, 2)); a = rng.randrange(w)
            b = a if op == 2 else rng.choice([x for x in range(w) if x != a])
            gates.append((op, min(a, b), max(a, b)))
        check_circuit(n, gates, stats); stats['circuits'] += 1


def chain_rank(t):
    """Rank-one chain on 4t inputs: data a_i (4i), c_i (4i+2); query b_i (4i+1), d_i (4i+3)."""
    n = 4 * t; full = (1 << (1 << n)) - 1
    var = lambda v: sum(1 << r for r in range(1 << n) if r >> v & 1)
    g = 0
    for i in range(t):
        a, b, c, d = (var(4 * i + k) for k in range(4))
        g = (g ^ a ^ b) & (c ^ d)
    side = sum(1 << (4 * i + k) for i in range(t) for k in (0, 2))
    return anchored_mixed_rank(n, g, side)


def encoding_check(rng, trials, padded):
    """Pinned-circuit CNF: SAT iff structural count >= floor, for floors count and count + 1."""
    checked = 0
    for _ in range(trials):
        n = rng.choice((3, 4, 5)); G = rng.randint(n - 1, n + 3)
        while True:  # random circuit using every wire, output = last gate, operands left <= right
            gates = []
            for j in range(G):
                w = n + j; op = rng.choice((0, 1, 2)); a = rng.randrange(w)
                b = a if op == 2 else rng.choice([x for x in range(w) if x != a])
                gates.append((op, min(a, b), max(a, b)))
            used = {x for _, a, b in gates for x in (a, b)}
            if all(i in used for i in range(n + G - 1)) or padded:
                break
        out = n + G - 1
        side = rng.randrange(1, (1 << n) - 1)
        count = structural_mixed_counts(n, gates, out, side)
        for floor in (0, count, count + 1):
            output, pool, clauses, ops, select = cs.build(n, G, colex_from=G, require_used=not padded)
            roots = None
            if padded:
                roots = {j: pool.id(('out', j)) for j in ops}
                clauses.extend([[roots[j]] if j == out else [-roots[j]] for j in ops])
            if floor:
                add_mixed_rank_cuts(n, output, pool, ops, select, clauses, [(floor, 0, side)],
                                    cone_root=roots)
            for j, (op, a, b) in enumerate(gates, start=n):
                clauses.extend([[ops[j][op]], [select[j, 0][a]], [select[j, 1][b]]])
            with Solver(name='maplechrono', bootstrap_with=clauses) as s:
                got = s.solve()
            if floor == 0:
                if not got:
                    break  # pinned circuit breaks a base rule of build (e.g. NOT of NOT); skip it
                continue
            want = floor <= count
            if got != want:
                raise AssertionError(f'encoding mismatch padded={padded} gates={gates} side={side:b} '
                                     f'floor={floor} count={count} sat={got}')
            checked += 1
    return checked


def corpus_check():
    from synthesis_cases import corpus, full_rows
    rows, worst = 0, []
    for case in corpus():
        if case.known != full_rows(case.n):
            continue
        cuts = cut_floors(case.n, case.truth)
        gates = [tuple(g) for g in case.witness.gates]
        for floor, rank, side in cuts:
            c = structural_mixed_counts(case.n, gates, case.witness.output, side)
            assert c >= floor, (case.name, side, rank, c)
        rows += 1
        best = cuts[0] if cuts else (0, 0, 0)
        worst.append((case.name, case.n, len(gates), best[0], best[1]))
    return rows, worst


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--exhaustive-gates', type=int, default=3)
    ap.add_argument('--random', type=int, default=20000)
    ap.add_argument('--encoding', type=int, default=150)
    ap.add_argument('--seed', type=int, default=20261126)
    ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    rng = random.Random(a.seed); t0 = time.time()
    k = 0
    for _ in range(300):
        n = rng.randint(2, 7); t = rng.getrandbits(1 << n); side = rng.randrange(1, (1 << n) - 1)
        assert anchored_mixed_rank(n, t, side) == dense_rank(n, t, side); k += 1
    print(f'rank vs dense reference: {k} random tables agree')
    assert [mixed_floor(r) for r in (0, 1, 2, 3, 6, 7, 14, 15)] == [0, 1, 1, 2, 2, 3, 3, 4]
    print('sharp chain ranks:', [chain_rank(t) for t in (1, 2, 3)], '(expect 2, 6, 14)')
    assert [chain_rank(t) for t in (1, 2, 3)] == [2, 6, 14]
    stats = dict(circuits=0, cuts=0, tight=0)
    exhaustive(4, a.exhaustive_gates, stats)
    print(f'exhaustive n=4 G<={a.exhaustive_gates}: {stats}')
    stats = dict(circuits=0, cuts=0, tight=0)
    random_circuits(a.random, rng, stats)
    print(f'random n=5..6 G=3..9: {stats}')
    print('encoding exact:', encoding_check(rng, a.encoding, False), 'pinned CNFs;',
          'padded/cone:', encoding_check(rng, a.encoding, True), 'pinned CNFs')
    rows, worst = corpus_check()
    print(f'corpus witnesses satisfy all cut floors: {rows} complete cases')
    if a.v:
        for w in sorted(worst, key=lambda w: -w[3]):
            print('  ', w)
    print(f'all checks passed in {time.time() - t0:.1f}s')
