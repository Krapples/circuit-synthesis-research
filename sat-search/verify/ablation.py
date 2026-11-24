"""Matched rule ablation on reference-decided workloads.

Workload: for each instance whose reference minimum M is decided, the exclusion at G = M - 1 (the UNSAT proof,
where pruning matters) and the search at G = M, over the complete first-gate cube set. Every configuration is
run on the same (instance, basis, G) jobs, one process per job, cubes sequential. Per job it records
  preprocessing = wall time minus SAT time (encoding, analytical bounds),
  rejection     = cubes refuted analytically before SAT,
  SAT time and conflicts (summed over cubes), total wall time, and the verdict (must match the reference).
Configurations: plain, each rule alone (with prerequisites), the --fast set, and --fast minus each of its rules
(leave-one-out shows whether a rule earns its cost inside the recommended set).
Usage: python verify/ablation.py [--quick] [--workers 11] [--kinds graph,hyper3] [--run NAME]"""
import argparse, json, os, re, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE); sys.path.insert(0, ROOT)
import warnings
warnings.filterwarnings('ignore')
import reference as ref
import differential as dif
import cube_search as cs

FAST = ('sens', 'units', 'usens', 'bypass', 'elim', 'elimclosure', 'signeddom', 'recursivebounds', 'notbypass',
        'recclosure', 'identifybounds', 'fanoutelim', 'pairro', 'colorbounds', 'sharecolor', 'colorbudget')
DEPENDS = {'usens': 'readonce', 'bypass': 'readonce', 'signeddom': 'bypass', 'notbypass': 'bypass',
           'elimclosure': 'elim', 'fanoutelim': 'elimclosure', 'recclosure': 'recursivebounds',
           'identifybounds': 'recursivebounds', 'colorbounds': 'recursivebounds', 'pairro': 'readonce',
           'sharecolor': 'readonce', 'colorbudget': 'readonce'}


def leave_one_out(base):
    out = {}
    for r in FAST:
        drop = {r} | {x for x in FAST if DEPENDS.get(x) == r}
        drop |= {x for x in FAST if DEPENDS.get(x) in drop}
        spec = dict(base, flags={k: v for k, v in base['flags'].items() if k not in drop})
        out[f'fast-{r}'] = spec
    for part in ('fanout', 'readonce', 'symmetry'):
        spec = dict(base, **{part: False})
        if part == 'readonce':
            spec['flags'] = {k: v for k, v in base['flags'].items()
                             if DEPENDS.get(k) not in ('readonce', 'bypass') and k not in ('usens', 'bypass')}
        out[f'fast-{part}'] = spec
    return out


def job(args):
    name, spec, n, terms, kind, basis, G, expect = args
    t0 = time.time()
    tt = ref.truth_table(n, terms)
    try:
        flags = dif.build_flags(spec, n, terms, basis, G, ())
        t_flags = time.time() - t0
        cubes = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]
        if basis == 'general':
            cubes += [(2, i, i) for i in range(n)]
        if spec['symmetry']:
            auts = cs.automorphisms(n, [tuple(i for i in range(n) if t >> i & 1) for t in terms])
            cubes = [c for c in cubes if cs.orbit_min(c, auts)]
        sat_t = conf = analytical = 0
        verdict = 'UNSAT'
        for c in cubes:
            _, st, circ, dt, info = cs.run_cube((n, list(terms), G, 'maplechrono', c, spec['fanout'],
                                                 spec['readonce'], dict(flags)))
            info = str(info)
            if info.startswith('analytical'):
                analytical += 1
            m = re.search(r'solve=([\d.]+)s', info)
            sat_t += float(m.group(1)) if m else 0.0
            m = re.search(r'conflicts=(\d+)', info)
            conf += int(m.group(1)) if m else 0
            if st == 'WITNESS':
                ok = ref.check_witness(n, tt, [tuple(g) for g in circ], (), True, basis)
                verdict = 'SAT' if ok else 'BADWITNESS'
                break
            if st != 'UNSAT':
                verdict = st
                break
        total = time.time() - t0
        return dict(config=name, kind=kind, n=n, terms=list(terms), basis=basis, G=G, expect=expect,
                    verdict=verdict, ok=verdict == expect, cubes=len(cubes), analytical=analytical,
                    sat_seconds=round(sat_t, 3), conflicts=conf, port_setup_seconds=round(t_flags, 3),
                    preprocessing_seconds=round(total - sat_t, 3), total_seconds=round(total, 3))
    except Exception as e:
        return dict(config=name, kind=kind, n=n, terms=list(terms), basis=basis, G=G, expect=expect,
                    verdict='ERROR', ok=False, error=repr(e))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--kinds', default='graph')
    ap.add_argument('--run', default=time.strftime('ablation-%Y%m%d-%H%M%S'))
    a = ap.parse_args()
    t0 = time.time()
    C = dif.configs()
    singles = {k: v for k, v in C.items() if not k.startswith('fast') and k not in ('minimal', 'reuse', 'units')}
    configs = {**singles, 'fast': C['fast'], **leave_one_out(C['fast'])}
    cache = dif.load_ref_cache()
    kinds = set(a.kinds.split(','))
    jobs = []
    for kind, n, t in dif.instances(a.quick):
        if kind not in kinds:
            continue
        for b in ('monotone', 'general'):
            r = cache.get((n, t, b))
            if not r or r['minimum'] is None or r['minimum'] < 2:
                continue
            for name, spec in configs.items():
                if b not in spec['bases'] or (spec['graph'] and kind != 'graph'):
                    continue
                for G, expect in ((r['minimum'] - 1, 'UNSAT'), (r['minimum'], 'SAT')):
                    jobs.append((name, spec, n, t, kind, b, G, expect))
    os.makedirs(os.path.join(ROOT, 'results', 'ablation'), exist_ok=True)
    path = os.path.join(ROOT, 'results', 'ablation', f'{a.run}.jsonl')
    out = open(path, 'w', encoding='utf-8')
    out.write(json.dumps(dict(header=True, run=a.run, version=dif.source_version(), argv=sys.argv,
                              configs=sorted(configs), jobs=len(jobs))) + '\n')
    print(f'{len(jobs)} jobs, {len(configs)} configurations', flush=True)
    rows = []
    with Pool(a.workers, maxtasksperchild=50) as p:
        for r in p.imap_unordered(job, jobs, chunksize=2):
            out.write(json.dumps(r) + '\n'); rows.append(r)
            if not r['ok']:
                print('MISMATCH', r, flush=True)
    out.close()
    # summary per configuration (matched: every configuration ran the same jobs within its bases)
    agg = {}
    for r in rows:
        if 'total_seconds' not in r:
            continue
        g = agg.setdefault((r['config'], r['basis']), dict(jobs=0, total=0.0, sat=0.0, pre=0.0, conf=0, rej=0, cubes=0))
        g['jobs'] += 1; g['total'] += r['total_seconds']; g['sat'] += r['sat_seconds']
        g['pre'] += r['preprocessing_seconds']; g['conf'] += r['conflicts']; g['rej'] += r['analytical']
        g['cubes'] += r['cubes']
    print(f'{"config":24} {"basis":9} {"jobs":>5} {"total s":>8} {"SAT s":>8} {"pre s":>8} {"conflicts":>10} '
          f'{"rejected/cubes":>15}')
    for (c, b), g in sorted(agg.items(), key=lambda kv: (kv[0][1], kv[1]['total'])):
        print(f'{c:24} {b:9} {g["jobs"]:5} {g["total"]:8.1f} {g["sat"]:8.1f} {g["pre"]:8.1f} {g["conf"]:10} '
              f'{g["rej"]:>7}/{g["cubes"]:<7}')
    print(f'records: {path} ({time.time() - t0:.0f}s)')
