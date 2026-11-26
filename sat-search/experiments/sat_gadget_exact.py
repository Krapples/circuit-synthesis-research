"""Exact-size scoring of composable restriction blocks for the pequalnp SAT encoding.

Background (NOTES_SAT_ENCODING_BOUNDS.md, six-bit fragment review): for a coordinate restriction rho of SAT_n with
m essential free bits, B(SAT_n) >= n - m + C(SAT_n|rho) in the free-NOT binary (AIG) count, provided all n
coordinates of SAT_n are essential. If SAT(B(z_1) ... B(z_q) tail) = AND_i f(z_i) and C(AND_i f(z_i)) =
q (C(f) + 1) - 1, then B(SAT_n) >= n - 1 + q e with e = C(f) + 1 - m, i.e. coefficient 1 + e / L for a block of
length L. The block T(x, y) = 11x10y with tail 110100 has f = XNOR, C = 3, e = 2, e / L = 1/3 (the 4n/3 bound).

This script searches blocks of length L <= --max-len with m <= 4 free coordinates (all other bits fixed) and a
tail from TAILS. For every block it requires that f depends on all m free bits, scores it by exact C(f) (Percy
ladder below the cofactor library witness, cached per NPN class), and for the best blocks checks the composition
identity exhaustively for q = 2 and q = 3. What it does NOT establish: the composition identity for all q, the
additivity C(AND) = q (C + 1) - 1 (proved only for XNOR blocks), or full support of SAT_n at the composed length.
Every score is therefore a candidate coefficient, not a lower bound.
"""
import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
from pathlib import Path
from time import perf_counter

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'baselines'))
sys.path.insert(0, str(HERE))
import first_layer_check as F  # noqa: E402
from sat_encoding_bound_review import parse, sat  # noqa: E402  (decoder written from Defs/Search.lean)
from witness_import import Library  # noqa: E402

TAILS = ('', '00', '110100')
MODE = 'slack-three-phase-set-lift1-count-const-liveall-ess-cond'


def word(w, L):
    return ''.join('1' if (w >> (L - 1 - j)) & 1 else '0' for j in range(L))  # axis j <-> position j


def sat_table(L, tail):
    return np.array([sat(word(w, L) + tail) for w in range(1 << L)], dtype=np.uint8).reshape((2,) * L)


def full_support(m):
    ok = set()
    for f in range(1 << (1 << m)):
        if all(any(((f >> r) & 1) != ((f >> (r ^ (1 << i))) & 1) for r in range(1 << m)) for i in range(m)):
            ok.add(f)
    return ok


def embed4(m, f):
    """Truth table over 4 inputs of an m-input function (extra inputs ignored)."""
    return sum(((f >> (x & ((1 << m) - 1))) & 1) << x for x in range(16))


def blocks(L, tail, m, support):
    """Unique (tt, template) per tt for blocks of length L with m free coordinates."""
    arr = sat_table(L, tail)
    weights = (1 << np.arange(1 << m, dtype=np.int64))
    out = {}
    for S in combinations(range(L), m):
        rest = [j for j in range(L) if j not in S]
        rows = np.moveaxis(arr, list(reversed(S)), list(range(L - m, L))).reshape(-1, 1 << m).astype(np.int64)
        tts = rows @ weights
        uniq, first = np.unique(tts, return_index=True)
        for tt, idx in zip(uniq.tolist(), first.tolist()):
            if tt not in support or tt in out:
                continue
            t = ['?'] * L
            for k, j in enumerate(rest):
                t[j] = str((idx >> (len(rest) - 1 - k)) & 1)
            for i, j in enumerate(S):
                t[j] = 'abcdef'[i]
            out[tt] = ''.join(t)
    return out


def fill(template, z):
    return ''.join(str(z[ord(c) - 97]) if c.isalpha() else c for c in template)


def composes(template, tail, m, f, q):
    for zs in product(product((0, 1), repeat=m), repeat=q):
        want = all((f >> sum(b << i for i, b in enumerate(z))) & 1 for z in zs)
        if sat(''.join(fill(template, z) for z in zs) + tail) != want:
            return False
    return True


START = ('B', False, False, False, False)  # (phase, last digit 0, clause nonempty, clause has +, literal is +)
UNCERTIFIED = 'all-negative clause'


def step(state, tok):
    """One token of the encodeCNF grammar. Returns the next state, None for a definite reject (grammar error or
    an empty clause, which is unsatisfiable whatever follows), or UNCERTIFIED when a nonempty clause with no
    positive literal closes (the all-true assignment no longer certifies satisfiability)."""
    phase, last0, nonempty, haspos, pol = state
    if phase == 'B':
        if tok == '00':
            if not nonempty:
                return None
            return ('B', False, False, False, False) if haspos else UNCERTIFIED
        if tok == '01':
            return None
        return ('P', False, nonempty, haspos, tok == '11')
    if tok == '00':
        return None
    if tok == '01':
        return None if (phase == 'D' and last0) else ('B', False, True, haspos or pol, False)
    return ('D', tok == '10', nonempty, haspos, pol)


def run_tokens(state, s):
    for i in range(0, len(s), 2):
        state = step(state, s[i:i + 2])
        if state is None or state == UNCERTIFIED:
            return state
    return state


def induction_certificate(template, tail, m, f):
    """Finite proof that SAT(B(z_1) ... B(z_q) tail) = AND_i f(z_i) for every q >= 1. Over the states R reachable
    at block boundaries: acceptance of each block is state-independent and equals f, every closed clause has a
    positive literal (so the all-true assignment satisfies every valid word; empty clauses are rejects), and the
    tail reaches the accepting state from every state of R. Induction on q then gives the identity: a word is
    valid with every clause positive iff every block accepts, and validity then implies satisfiability, while an
    invalid word or one with an empty clause is rejected by SAT. Returns None on success, else the failure."""
    if len(template) % 2 or len(tail) % 2:
        return 'odd length'
    R, frontier = {START}, [START]
    while frontier:
        st = frontier.pop()
        for z in product((0, 1), repeat=m):
            nxt = run_tokens(st, fill(template, z))
            if nxt == UNCERTIFIED:
                return UNCERTIFIED
            if nxt is not None and nxt not in R:
                R.add(nxt); frontier.append(nxt)
    for z in product((0, 1), repeat=m):
        ok = {run_tokens(st, fill(template, z)) is not None for st in R}
        if len(ok) != 1:
            return 'state-dependent acceptance'
        if ok.pop() != bool((f >> sum(b << i for i, b in enumerate(z))) & 1):
            return 'acceptance differs from f'
    for st in R:
        if run_tokens(st, tail) != START:
            return 'tail fails from a reachable state'
    return None


def automaton_selftest(max_len=14):
    """The automaton must agree with the reviewed parser: START at the end iff the word parses with every clause
    containing a positive literal; a definite reject only for words SAT rejects."""
    checked = 0
    for L in range(0, max_len + 1, 2):
        for w in range(1 << L):
            s = word(w, L)
            end, cnf = run_tokens(START, s), parse(s)
            if end == START:
                assert cnf is not None and all(any(p for _, p in c) for c in cnf) and sat(s), s
            elif end is None:
                assert not sat(s), s
            elif end == UNCERTIFIED:
                assert cnf is None or any(c and not any(p for _, p in c) for c in cnf), s
            else:  # unfinished word
                assert cnf is None, s
            checked += 1
    return checked


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('out', type=Path)
    p.add_argument('--max-len', type=int, default=14)
    p.add_argument('--max-free', type=int, default=4)
    p.add_argument('--top', type=int, default=40, help='composition checks for this many best blocks')
    p.add_argument('--cache', type=Path, default=HERE.parent / 'results/sat_gadget/npn4_exact_aig.json')
    p.add_argument('--tier', default='extended', choices=tuple(F.TIERS))
    p.add_argument('--workers', type=int, default=10)
    a = p.parse_args()
    t0 = perf_counter()
    print(f'automaton self-test: {automaton_selftest()} words', flush=True)
    lib = Library(HERE.parent / 'results/cofactor_witness/npn4_witnesses.json')
    cache = json.loads(a.cache.read_text()) if a.cache.exists() else {}
    found = []  # (L, tail, m, tt, template, rep)
    for L in range(2, a.max_len + 1, 2):
        for tail in TAILS:
            for m in range(2, min(a.max_free, L) + 1):
                for tt, template in blocks(L, tail, m, full_support(m)).items():
                    found.append((L, tail, m, tt, template, lib.index[embed4(m, tt)][0]))
        print(f'L={L} blocks={len(found)} {perf_counter() - t0:.1f}s', flush=True)

    seconds, conflicts = F.TIERS[a.tier]
    need = sorted({rep for *_, rep in found if f'{rep:04x}' not in cache})

    def exact(rep):
        w = lib.chain(rep)
        r = F.run(F.PERCY, MODE, f'gadget-{rep:04x}', 4, rep, 0xffff, 'cegar', seconds, conflicts,
                  start=1, upper_witness=w['spec'])
        return rep, {'upper': r['upper_bound'], 'open_budget': r['open_budget'], 'status': r['status'],
                     'witness': w['size'], 'seconds': round(r['wall_seconds'], 3)}

    with ThreadPoolExecutor(a.workers) as pool:
        for rep, rec in pool.map(exact, need):
            cache[f'{rep:04x}'] = rec
    a.cache.parent.mkdir(parents=True, exist_ok=True)
    a.cache.write_text(json.dumps(cache, indent=0, sort_keys=True) + '\n')

    rows = []
    for L, tail, m, tt, template, rep in found:
        c = cache[f'{rep:04x}']
        exact_c = c['upper'] if c['open_budget'] is None else None
        lo = exact_c if exact_c is not None else c['open_budget']  # all budgets below open_budget are UNSAT
        rows.append({'L': L, 'tail': tail, 'm': m, 'tt': f'{tt:0{max(1, (1 << m) // 4)}x}', 'template': template,
                     'npn4_rep': f'{rep:04x}', 'C': exact_c, 'C_lower': lo, 'C_upper': c['upper'],
                     'e_lower': lo + 1 - m, 'ratio_lower': (lo + 1 - m) / L})
    rows.sort(key=lambda r: (-r['ratio_lower'], r['L'], r['m']))
    for r in rows[:a.top]:
        f = int(r['tt'], 16)
        r['compose_q2'] = composes(r['template'], r['tail'], r['m'], f, 2)
        r['compose_q3'] = composes(r['template'], r['tail'], r['m'], f, 3) if r['compose_q2'] else False
        fail = induction_certificate(r['template'], r['tail'], r['m'], f)
        r['compose_all_q'] = fail is None
        r['compose_fail'] = fail
        if r['compose_all_q'] and not r['compose_q3']:
            raise AssertionError(('certificate contradicts exhaustive check', r))
    with a.out.open('w') as out:
        for r in rows:
            out.write(json.dumps(r) + '\n')
    best = [r for r in rows[:a.top] if r.get('compose_all_q')]
    print(json.dumps({'blocks': len(rows), 'npn_classes': len({r['npn4_rep'] for r in rows}),
                      'open_classes': sorted(k for k, v in cache.items() if v['open_budget'] is not None),
                      'seconds': round(perf_counter() - t0, 1),
                      'best_composing': [{k: r[k] for k in ('L', 'tail', 'm', 'tt', 'template', 'C', 'e_lower',
                                                            'ratio_lower')} for r in best[:12]]}, indent=1))


if __name__ == '__main__':
    main()
