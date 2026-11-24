"""Evidence ledger: keeps the kinds of support for a verdict apart and decides what may be reported.

Evidence kinds, per cube:
  witness          a circuit checked on every row by reference.check_witness (gives an upper bound / SAT);
  checked_unsat    a CNF plus a DRUP proof accepted by the independent RUP checker
                   (experiments/certify_synthesis.check_proof); the CNF comes from the reference encoder, so
                   its model is the claimed one (no pruning rules involved);
  analytical       cube_search rejected the cube before SAT with a named bound (recorded with the rule text);
                   valid only to the extent the bound has differential coverage (verify/AUDIT.md);
  unchecked_unsat  a SAT solver returned UNSAT with rules enabled and no checked proof;
  open             timeout, interrupt or error: the budget stays open.

An exclusion of exact size G in a scope (whole function, or a pinned prefix) needs exhaustive cube coverage:
the recorded cube set must equal the enumeration for that scope. Its grade is
  certified       every cube checked_unsat (or the whole scope checked_unsat in one CNF);
  rule-dependent  every cube excluded, some analytically or unchecked (a verified computational result whose
                  correctness rests on the rules' proofs and their differential coverage);
  open            otherwise.
A minimum M is reported as CERTIFIED only with a verified witness at M and certified exclusions at M - 1
and M - 2, for a function with every input essential and n >= 2. The padding step (exact size s implies
exact size s + 2 by appending AND(x0, out), OR(out, that gate)) needs a wire other than the output, i.e.
n + s >= 2; with n >= 2 this holds for every s, while one input and no gates is the excluded boundary case
(verify/test_theory.py). Anything weaker is reported with its grade.

Usage: python verify/evidence.py --n 4 --terms 3,6,12 --basis monotone [--fast] [--out ledger.jsonl]"""
import argparse, hashlib, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, ROOT); sys.path.insert(0, os.path.join(ROOT, 'experiments'))
import reference as ref
from certify_synthesis import check_proof
import differential as dif
import cube_search as cs


def sha(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode()).hexdigest()[:16]


def checked_exclusion(n, terms, G, basis, prefix=()):
    """Whole-scope exclusion by the reference encoder with a DRUP proof checked by the RUP checker."""
    tt = ref.truth_table(n, terms)
    t0 = time.time()
    w, info = ref.sat_exists(n, tt, G, basis, prefix, proof=True)
    if w is not None:
        return dict(kind='witness', circuit=w, verified=ref.check_witness(n, tt, w, prefix, True, basis))
    if info.get('trivial'):
        return dict(kind='checked_unsat', trivial=info.get('reason', 'no gate choice'), seconds=0)
    cnf, proof = info['cnf'], list(info['proof'])
    # A solver that refutes by top-level propagation may stop before writing the empty clause; append it.
    # The checker still has to derive it by reverse unit propagation, so nothing is taken on trust.
    if not proof or proof[-1].split() != ['0']:
        proof.append('0')
    steps = check_proof(info['vars'], cnf, proof)
    return dict(kind='checked_unsat', cnf_sha=sha(cnf), proof_sha=sha(proof), proof_steps=steps,
                cnf_clauses=len(cnf), solver=info['solver'], checker='certify_synthesis.check_proof (RUP)',
                seconds=round(time.time() - t0, 2))


def cube_search_exclusion(n, terms, G, basis, spec):
    """Per-cube cube_search verdicts over the complete first-gate cube set of the configuration."""
    masks = list(terms)
    tt = ref.truth_table(n, terms)
    cubes = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]
    if basis == 'general':
        cubes += [(2, i, i) for i in range(n)]
    auts = None
    if spec['symmetry']:
        auts = cs.automorphisms(n, [tuple(i for i in range(n) if t >> i & 1) for t in terms])
        cubes = [c for c in cubes if cs.orbit_min(c, auts)]
    flags = dif.build_flags(spec, n, terms, basis, G, ())
    per = []
    for c in cubes:
        _, st, circ, dt, info = cs.run_cube((n, masks, G, 'maplechrono', c, spec['fanout'], spec['readonce'],
                                             dict(flags)))
        if st == 'WITNESS':
            ok = ref.check_witness(n, tt, [tuple(g) for g in circ], (), True, basis)
            per.append(dict(cube=c, kind='witness', circuit=circ, verified=ok))
        elif st == 'UNSAT':
            kind = 'analytical' if str(info).startswith('analytical') else 'unchecked_unsat'
            per.append(dict(cube=c, kind=kind, detail=str(info)[:200], seconds=round(dt, 3)))
        else:
            per.append(dict(cube=c, kind='open', detail=f'{st} {info}'[:200]))
    coverage = dict(enumeration='first gate (op, l, r), l < r < n' + (', NOT cubes' if basis == 'general' else ''),
                    symmetry=bool(auts), automorphisms=len(auts) if auts else 1, cubes=len(cubes))
    return per, coverage


def grade(per):
    kinds = {p['kind'] for p in per}
    if 'witness' in kinds:
        return 'sat' if all(p.get('verified', True) for p in per if p['kind'] == 'witness') else 'bad-witness'
    if 'open' in kinds or not per:
        return 'open'
    if kinds == {'checked_unsat'}:
        return 'certified'
    return 'rule-dependent'


def certify_minimum(n, terms, basis, spec=None, gmax=None, reference_proofs=True):
    """Find the minimum with cube_search, then grade the witness and the M-1, M-2 exclusions."""
    tt = ref.truth_table(n, terms)
    if len(ref.essential_inputs(n, tt)) != n:
        raise ValueError('every input must be essential (contract for the exact-G model)')
    if n < 2:
        raise ValueError('n >= 2 required: padding by two gates needs a wire other than the output')
    spec = spec or dif.configs()['plain']
    records = []
    gmax = gmax or 4 * n
    M = None
    for G in range(n - 1, gmax + 1):
        per, cov = cube_search_exclusion(n, terms, G, basis, spec)
        g = grade(per)
        records.append(dict(G=G, source='cube_search', grade=g, coverage=cov, cubes=per))
        if g in ('sat', 'bad-witness'):
            M = G
            break
        if g == 'open':
            break
    out = dict(n=n, terms=list(terms), basis=basis, config=spec, minimum_found=M, records=records,
               version=dif.source_version())
    if M is None or records[-1]['grade'] != 'sat':
        out['report'] = 'no verified minimum'
        return out
    lower = {}
    for G in (M - 1, M - 2):
        if G < n - 1:
            lower[G] = dict(grade='certified', reason='below n - 1: n + G - 1 wires cannot all be read with 2G slots')
            continue
        if reference_proofs:
            ev = checked_exclusion(n, terms, G, basis)
            lower[G] = dict(grade='certified' if ev['kind'] == 'checked_unsat' else 'CONTRADICTION', evidence=ev)
        else:
            lower[G] = dict(grade=next(r['grade'] for r in records if r['G'] == G))
    out['lower'] = lower
    grades = {v['grade'] for v in lower.values()}
    if grades == {'certified'}:
        out['report'] = f'CERTIFIED minimum {M} (verified witness; checked exclusions at {M - 1}, {M - 2})'
    elif 'CONTRADICTION' in grades:
        out['report'] = 'CONTRADICTION: reference found a circuit below the cube_search minimum'
    else:
        out['report'] = f'minimum {M} rule-dependent (exclusions not all checked)'
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--terms', required=True, help='comma-separated bitmasks, or edges u-v')
    ap.add_argument('--basis', choices=('monotone', 'general'), default='monotone')
    ap.add_argument('--config', default='plain')
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    items = a.terms.split(',')
    terms = (ref.graph_terms(a.n, [tuple(map(int, e.split('-'))) for e in items]) if '-' in a.terms
             else ref.normalize_terms(a.n, [int(x) for x in items]))
    res = certify_minimum(a.n, terms, a.basis, dif.configs()[a.config])
    print(res['report'])
    for G, v in sorted(res.get('lower', {}).items()):
        print(f'  size {G}: {v["grade"]} {json.dumps(v.get("evidence", v.get("reason", "")))[:160]}')
    if a.out:
        with open(a.out, 'a', encoding='utf-8') as f:
            f.write(json.dumps(res, default=str) + '\n')
