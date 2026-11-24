"""Differential test of cube_search's analytical lower bounds against reference minima (verify/reference.py).

Every bound must be <= the exact minimum it claims to bound (binary-gate bounds are compared with the total
gate count of the reference minimum, a necessary condition):
  whole function : rec_lb (depth 0..3), port_binary_lb for every port-cost recipe, ordered_type_bounds,
                   under every setting of the module switches MONO / REC_CLOSURE / COLOR_BOUNDS / ORDERED
                   (MONO only against the monotone minimum);
  first gate     : cube_binary_lb (depth 1, 2; identify on/off; with/without port costs) against the reference
                   minimum over circuits starting with that gate;
  two input gates: multi_gate_lb against the reference minimum with both gates pinned;
  pinned prefix  : ordered_prefix_bound, partial_repeat_bound, partial_multiplicity_bound (every split, with and
                   without empty regions and coupled projections), frontier_requirements, for random monotone
                   prefixes of 1..5 gates (from reference witnesses and random gates).
Usage: python verify/bounds_check.py [--quick] [--workers 11] [--run NAME]"""
import argparse, json, os, random, sys, time, traceback
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, ROOT)
import warnings
warnings.filterwarnings('ignore')
import reference as ref
import differential as dif
import cube_search as cs

OUT = os.path.join(ROOT, 'results', 'bound_differential')


def port_recipes(basis):
    out = {'plain': dict(), 'formula_polarity': dict(formula=True, polarity=True)}
    if basis == 'monotone':
        out.update({
            'mono_sep': dict(mono=True, separation=True),
            'mono_full': dict(mono=True, separation=True, profile=True, formula=True, output=True),
            'cert_compat': dict(mono=True, certificate_level='compatibility'),
            **{f'cert_{l}': dict(mono=True, certificate_level=l) for l in cs.PORT_CERTIFICATE_LEVELS},
            'cert_output': dict(mono=True, certificate_level='rank', certificate_output=True),
            'providers': dict(mono=True, certificate_level='rank', provider_eligibility=True),
            'type_rank': dict(mono=True, type_rank=True),
        })
    return out


def set_switches(mono, closure, color, ordered):
    cs.MONO[0], cs.REC_CLOSURE[0], cs.COLOR_BOUNDS[0], cs.ORDERED[0] = mono, closure, color, ordered


def prefix_minimum(n, tt, basis, P, M, cap=3):
    for G in range(max(len(P), M), M + cap + 1):
        w, info = ref.sat_exists(n, tt, G, basis, P, seconds=dif.REF_SECONDS)
        if info.get('undecided'):
            return None            # unknown limit: the bound is recorded but not judged
        if w is not None:
            return G
    return None


def topo_prefixes(n, witness, rng, count, kmax):
    out = []
    G = len(witness)
    for _ in range(count):
        placed, order = set(), []
        while len(order) < G:
            ready = [j for j in range(G) if j not in placed and all(a < n or a - n in placed for a in witness[j][1:])]
            j = rng.choice(ready)
            placed.add(j); order.append(j)
        pos = {n + j: n + k for k, j in enumerate(order)}
        rl = lambda a: a if a < n else pos[a]
        rel = []
        for j in order:
            op, a, b = witness[j]
            rel.append((op, rl(a), rl(b)) if op == 2 else (op, *sorted((rl(a), rl(b)))))
        out.append(tuple(rel[:rng.randint(1, min(kmax, G - 1))]))
    return out


def check_instance(args):
    kind, n, terms, refs, seed, quick = args
    rng = random.Random(seed)
    masks = tuple(terms)
    T = cs._anti(list(masks))
    recs, viol = [], []

    def rec(test, value, bound_of, limit, **kw):
        r = dict(kind=kind, n=n, terms=list(terms), test=test, value=value, limit=limit, **kw)
        recs.append(r)
        if value is not None and limit is not None and value != float('inf') and value > limit:
            viol.append(r)
        elif value == float('inf') and limit is not None:
            viol.append(r)

    try:
        for basis in ('monotone', 'general'):
            M = refs[basis]['minimum']
            tt = ref.truth_table(n, terms)
            monos = (False, True) if basis == 'monotone' else (False,)
            recipes = port_recipes(basis)
            costs = {}
            for name, kw in recipes.items():
                try:
                    costs[name] = cs.port_costs(T, **kw)
                except Exception as e:
                    rec(f'port_costs[{name}]', None, None, None, basis=basis, error=repr(e))
            for mono in monos:
                for closure in (False, True):
                    for color in (False, True):
                        for ordered in (False, True):
                            set_switches(mono, closure, color, ordered)
                            sw = dict(mono=mono, closure=closure, color=color, ordered=ordered, basis=basis)
                            for d in range(4):
                                rec('rec_lb', cs.rec_lb(T, d), None, M, depth=d, **sw)
                            for name, c in costs.items():
                                if getattr(c, 'mono', False) and basis != 'monotone':
                                    continue
                                rec('port_binary_lb', cs.port_binary_lb(T, c), None, M, recipe=name, **sw)
                                if basis == 'monotone' and ordered:
                                    a, o, b = cs.ordered_type_bounds(T, c)
                                    rec('ordered_type_bounds', b, None, M, recipe=name, ands=a, ors=o, **sw)
            # first-gate bounds
            cubes = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]
            if basis == 'general':
                cubes += [(2, i, i) for i in range(n)]
            if quick:
                cubes = rng.sample(cubes, min(6, len(cubes)))
            set_switches(basis == 'monotone', True, True, True)
            for c in cubes:
                Mc = prefix_minimum(n, tt, basis, (c,), M)
                for d in (1, 2):
                    for ident in (False, True):
                        for pname in (None, 'plain', 'mono_full' if basis == 'monotone' else 'formula_polarity'):
                            pc = costs.get(pname) if pname else None
                            if pname and pc is None:
                                continue
                            v = cs.cube_binary_lb(list(masks), c, d, identify=ident, port=pc)
                            rec('cube_binary_lb', v, None, Mc, basis=basis, cube=c, depth=d, identify=ident,
                                port=pname)
            # two gates on inputs
            pairs = [(a, b) for a in cubes for b in cubes if a < b and a[0] != 2 and b[0] != 2]
            for a, b in rng.sample(pairs, min(4 if quick else 10, len(pairs))):
                P = (a, b)
                MP = prefix_minimum(n, tt, basis, P, M)
                for d in (1, 2):
                    rec('multi_gate_lb', cs.multi_gate_lb(list(masks), list(P), d), None, MP, basis=basis,
                        prefix=P, depth=d)
            # pinned-prefix bounds (monotone only)
            if basis == 'monotone':
                set_switches(True, False, False, False)
                w = [tuple(g) for g in refs[basis]['witness']]
                prefs = topo_prefixes(n, w, rng, 3 if quick else 8, 5)
                for _ in range(3 if quick else 8):
                    k = rng.randint(1, 5)
                    p = []
                    for j in range(k):
                        b = rng.randrange(1, n + j)
                        p.append((rng.choice((0, 1)), rng.randrange(b), b))
                    prefs.append(tuple(p))
                for P in prefs:
                    MP = prefix_minimum(n, tt, basis, P, M)
                    rec('ordered_prefix_bound', cs.ordered_prefix_bound(n, masks, P), None, MP, prefix=P)
                    if len(P) > 1:
                        rec('partial_repeat_bound', cs.partial_repeat_bound(n, masks, P[:-1], P[-1]), None, MP,
                            prefix=P)
                    for k in range(len(P)):
                        for empty in (False, True):
                            rec('partial_multiplicity_bound',
                                cs.partial_multiplicity_bound(n, masks, P[:k], list(P[k:]), empty=empty), None, MP,
                                prefix=P, split=k, empty=empty)
                    if len(P) >= 1 and n + len(P) <= cs.PARTIAL_FEATURE_LIMIT:
                        after = cs.repeat_prefix_projections(n, masks, P)
                        for k in range(len(P)):
                            rec('coupled_multiplicity',
                                cs.partial_multiplicity_bound(n, masks, P[:k], list(P[k:]), after=after), None, MP,
                                prefix=P, split=k)
                    rec('frontier_requirements', cs.frontier_requirements(n, masks, P, True)[0], None, MP,
                        prefix=P)
    except Exception as e:
        recs.append(dict(kind=kind, n=n, terms=list(terms), test='ERROR', error=repr(e),
                         trace=traceback.format_exc()[-800:]))
        viol.append(recs[-1])
    return recs, viol


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--run', default=time.strftime('bounds-%Y%m%d-%H%M%S'))
    a = ap.parse_args()
    t0 = time.time()
    os.makedirs(OUT, exist_ok=True)
    insts = dif.instances(a.quick)
    cache = dif.load_ref_cache()
    jobs = []
    for i, (kind, n, t) in enumerate(insts):
        refs = {b: cache.get((n, t, b)) for b in ('monotone', 'general')}
        if any(r is None or r['minimum'] is None for r in refs.values()):
            print('missing reference minimum, run differential.py first:', n, t)
            continue
        jobs.append((kind, n, t, refs, 1000 + i, a.quick))
    version = dif.source_version()
    out = open(os.path.join(OUT, f'{a.run}.jsonl'), 'w', encoding='utf-8')
    out.write(json.dumps(dict(header=True, run=a.run, version=version, instances=len(jobs), argv=sys.argv)) + '\n')
    total, bad = 0, []
    counts = {}
    with Pool(a.workers) as p:
        for recs, viol in p.imap_unordered(check_instance, jobs):
            for r in recs:
                out.write(json.dumps(r, default=str) + '\n')
                counts[r['test']] = counts.get(r['test'], 0) + 1
            total += len(recs)
            out.flush()
            if recs:
                print(f'  instance {recs[0]["kind"]} n={recs[0]["n"]} terms={recs[0]["terms"]}: {len(recs)} '
                      f'evaluations, {len(viol)} violations ({time.time() - t0:.0f}s)', flush=True)
            for v in viol:
                bad.append(v)
                print('VIOLATION', json.dumps(v, default=str)[:400], flush=True)
    out.close()
    print(f'DONE {len(jobs)} instances, {total} bound evaluations, {len(bad)} violations ({time.time() - t0:.0f}s)')
    print('evaluations per test:', counts)
