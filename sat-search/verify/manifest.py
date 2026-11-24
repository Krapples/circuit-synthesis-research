"""Independent verification of cube_search evidence manifests (cube_search.py --manifest PATH).

Checks, each reported separately:
  target     terms re-derived from the edge list with the input contract (verify/reference.graph_terms); every
             input essential; edge key consistent;
  sources    sha256 of each recorded source file against the current file (a mismatch does not invalidate
             the record but means re-checking analytical verdicts below used different code);
  coverage   the enumeration is recomputed from the model (first gates, plus NOT cubes in the general basis);
             every recorded automorphism is checked to map the term family onto itself, and for n <= 8 the
             recorded group must equal the brute-force group; the orbit-minimal selection is recomputed; no
             cube may be skipped by log lines; every selected cube needs a record;
  cubes      witnesses are re-checked on every row by the reference; analytical exclusions are re-derived by
             running cube_search with SAT disabled (only when sources match); solver UNSAT verdicts are
             unchecked (no proof in a CLI manifest) and make the exclusion rule-dependent.
Grade: 'sat' (verified witness), 'rule-dependent' (complete coverage, every cube excluded, at least one by an
unchecked or analytical verdict), 'certified' only with checked proofs (verify/evidence.py), else 'invalid'.
Usage: python verify/manifest.py MANIFEST.json [--recheck-analytical]"""
import argparse, hashlib, itertools, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, ROOT)
import reference as ref


class _NoSat(Exception):
    pass


def verify_manifest(m, recheck_analytical=False):
    rep = dict(problems=[], notes=[])
    bad = rep['problems'].append
    if m.get('schema') != 'cube_search-manifest/1':
        bad('unknown schema'); rep['grade'] = 'invalid'; return rep
    n = m['target']['n']
    edges = [tuple(e) for e in m['target']['edges']]
    try:
        terms = ref.graph_terms(n, edges)
    except ValueError as e:
        bad(f'target violates the input contract: {e}'); rep['grade'] = 'invalid'; return rep
    if sorted(terms) != sorted(m['target']['terms']):
        bad('recorded terms differ from the edge list')
    tt = ref.truth_table(n, terms)
    if len(ref.essential_inputs(n, tt)) != n:
        bad('not every input is essential (exact-G model contract)')
    # sources
    same = True
    for f, h in m['sources']['sha256'].items():
        p = os.path.join(ROOT, f)
        cur = hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
        if cur != h:
            same = False
            rep['notes'].append(f'source {f} differs from the recorded hash')
    rep['sources_match'] = same
    # coverage
    model, cov = m['model'], m['coverage']
    basis = model['basis']
    allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]
    if basis == 'general':
        allc += [(2, i, i) for i in range(n)]
    if sorted(map(tuple, cov['all_cubes'])) != sorted(allc):
        bad('recorded enumeration differs from the model enumeration')
    E = {frozenset(e) for e in edges}
    auts = [tuple(a) for a in cov['automorphisms']]
    for a in auts:
        if sorted(a) != list(range(n)) or {frozenset(a[v] for v in e) for e in E} != E:
            bad(f'recorded permutation {a} is not an automorphism')
    if cov['symmetry'] and n <= 8:
        true = sorted(p for p in itertools.permutations(range(n)) if {frozenset(p[v] for v in e) for e in E} == E)
        if sorted(auts) != true:
            bad(f'recorded group ({len(auts)}) differs from the brute-force group ({len(true)})')
    if not cov['symmetry'] and auts != [tuple(range(n))]:
        bad('symmetry off but a nontrivial group was recorded')

    def orbit_min(c, group):
        op, l, r = c
        key = lambda x, y: (max(x, y), min(x, y))
        return all(key(l, r) <= key(g[l], g[r]) for g in group) if op != 2 else all(l <= g[l] for g in group)
    selected = [c for c in allc if orbit_min(c, auts)]
    if sorted(map(tuple, cov['selected'])) != sorted(selected):
        bad('recorded selection differs from the recomputed orbit-minimal selection')
    if cov['skipped_by_logs']:
        bad(f'{len(cov["skipped_by_logs"])} cubes were skipped by log lines (no evidence)')
    records = {tuple(r['cube']): r for r in m['cubes']}
    # cubes
    kinds = []
    for c in selected:
        r = records.get(c)
        if r is None:
            if m['result'] == 'WITNESS':
                continue           # the run stopped at the first witness
            bad(f'cube {c} has no record'); continue
        if r['status'] == 'WITNESS':
            ok = r['circuit'] is not None and ref.check_witness(n, tt, [tuple(g) for g in r['circuit']], (), True,
                                                                basis)
            kinds.append('witness' if ok else 'bad-witness')
            if not ok:
                bad(f'cube {c}: witness fails the reference check')
        elif r['status'] == 'UNSAT':
            kinds.append(r['evidence'])
            if r['evidence'] == 'analytical' and recheck_analytical and same:
                if not recheck_cube(m, n, terms, c):
                    bad(f'cube {c}: analytical exclusion did not reproduce')
        else:
            kinds.append('open')
            bad(f'cube {c}: status {r["status"]}')
    if m['result'] == 'WITNESS':
        rep['grade'] = 'sat' if 'witness' in kinds and not rep['problems'] else 'invalid'
    elif rep['problems'] or 'open' in kinds:
        rep['grade'] = 'invalid'
    else:
        rep['grade'] = 'rule-dependent'
        rep['notes'].append(f'{kinds.count("analytical")} analytical and {kinds.count("unchecked_unsat")} unchecked '
                            f'solver exclusions; no checked proofs in a CLI manifest')
    rep['cubes'] = len(selected)
    return rep


def recheck_cube(m, n, terms, cube):
    """Re-derive an analytical exclusion with SAT disabled (the cube must be refuted before any encoding)."""
    import cube_search as cs
    cfg = m['configuration']
    saved = cs.build, cs.Solver

    def no_sat(*args, **kwargs):
        raise _NoSat()
    cs.build = cs.Solver = no_sat
    try:
        flags = {k: v for k, v in cfg.items() if isinstance(v, bool) and v and k not in ('symmetry', 'fanout', 'readonce')}
        flags['recdepth'] = cfg.get('recdepth', 2)
        if cfg.get('portbounds'):
            flags['portcosts'] = cs.port_costs(cs._anti(list(terms)), mono=cfg.get('monoports', False))
        _, st, _, _, info = cs.run_cube((n, list(terms), m['model']['size'], cfg.get('solver', 'maplechrono'), cube,
                                         cfg.get('fanout', False), cfg.get('readonce', False), flags))
        return st == 'UNSAT' and str(info).startswith('analytical')
    except _NoSat:
        return False
    finally:
        cs.build, cs.Solver = saved


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('manifest')
    ap.add_argument('--recheck-analytical', action='store_true')
    a = ap.parse_args()
    r = verify_manifest(json.load(open(a.manifest, encoding='utf-8')), a.recheck_analytical)
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['grade'] in ('sat', 'rule-dependent', 'certified') else 1)
