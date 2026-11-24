"""Differential test of the production command line (cube_search.py main) against the reference.

Each job runs `python cube_search.py --n N --edges ... --size G <flags> --workers 1` as a subprocess, so flag
parsing, prerequisite handling, port-cost construction, the capacity-allocation floor and certificate type
counts (computed only in main) and the cube enumeration are all exercised exactly as in production. The
RESULT line is parsed; a WITNESS circuit is re-checked with verify/reference.py.
Points per (graph, basis, flag set): M - 1 must be ALL UNSAT, M and M + 2 must give a verified WITNESS.
--minimal is run with evidence manifests (--manifest) produced by the same harness at M - 1 and M - 2.
Only graph functions are expressible on the command line (--edges).
Usage: python verify/cli_differential.py [--workers 11] [--only NAME,...] [--run NAME] [--job-seconds 120]"""
import argparse, json, os, re, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor, as_completed
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import reference as ref
import differential as dif

CLI = os.path.join(ROOT, 'cube_search.py')
MONO = '--monotone'
FAST = '--fast'
FLAGSETS = {
    'plain': ('', 'both'), 'symmetry': ('--symmetry', 'both'), 'units': ('--units', 'both'),
    'reuse': ('--reuse', 'both'), 'fanout': ('--fanout', 'both'), 'readonce': ('--readonce', 'both'),
    'sens': ('--sens', 'both'), 'parity': ('--readonce --parity', 'general'),
    'usens': ('--readonce --usens', 'both'), 'closedcone': ('--readonce --closedcone', 'both'),
    'bypass': ('--readonce --bypass', 'both'), 'outdec': ('--outdec', 'both'),
    'bottleneck': ('--readonce --bottleneck', 'both'), 'elim': ('--elim', 'both'),
    'strongbounds': ('--strongbounds', 'both'), 'elimbypass': ('--readonce --elim --bypass --elimbypass', 'both'),
    'elimlink': ('--elim --elimlink', 'both'), 'readersens': ('--readersens', 'both'),
    'readerbudget': ('--readonce --readerbudget', 'both'), 'elimclosure': ('--elim --elimclosure', 'both'),
    'signeddom': ('--readonce --bypass --signeddom', 'both'), 'recursivebounds': ('--recursivebounds', 'both'),
    'notbypass': ('--readonce --bypass --notbypass', 'general'),
    'recclosure': ('--recursivebounds --recclosure', 'both'),
    'identifybounds': ('--recursivebounds --identifybounds', 'both'),
    'fanoutelim': ('--readonce --elim --elimclosure --fanoutelim', 'both'),
    'lostreader': ('--readonce --elim --elimclosure --fanoutelim --lostreader', 'both'),
    'pairro': ('--readonce --pairro', 'both'), 'colorbounds': ('--recursivebounds --colorbounds', 'both'),
    'colorbudget': ('--readonce --colorbudget', 'both'), 'sharecolor': ('--readonce --sharecolor', 'both'),
    'activecolor': ('--readonce --sharecolor --activecolor', 'both'),
    'colorzero': ('--readonce --sharecolor --colorzero', 'both'),
    'isolatedcolor': ('--readonce --sharecolor --isolatedcolor', 'both'),
    'polaritydom': ('--readonce --bypass --parity --polaritydom', 'general'),
    'portbounds': ('--recursivebounds --portbounds', 'both'),
    'formulaports': ('--recursivebounds --portbounds --formulaports', 'general'),
    'monoports': ('--recursivebounds --portbounds --monoports', 'monotone'),
    'orderedports': ('--recursivebounds --portbounds --monoports --orderedports', 'monotone'),
    'portcert_compatibility': ('--portcertrank compatibility', 'monotone'),
    'portcert_rank': ('--portcertrank rank', 'monotone'), 'portcert_clique': ('--portcertrank clique', 'monotone'),
    'portcert_exact': ('--portcertrank exact', 'monotone'),
    'portcert_output': ('--portcertrank rank --portcertoutput', 'monotone'),
    'portproviders': ('--portproviders', 'monotone'),
    'capacity_deficit': ('--capacityallocation deficit', 'monotone'),
    'capacity_packing': ('--capacityallocation packing', 'monotone'),
    'capacity_exact': ('--capacityallocation exact', 'monotone'),
    'certtyperank': ('--certtyperank', 'monotone'),
    'cert': ('--cert', 'monotone'), 'frontier': ('--frontier', 'monotone'),
    'partialordered': ('--partialordered', 'monotone'), 'partialrepeat': ('--partialrepeat', 'monotone'),
    'partialmultiplicity': ('--partialmultiplicity', 'monotone'),
    'matchinginterface': ('--matchinginterface', 'monotone'),
    'fast': (FAST, 'both'), 'fast+cert': (f'{FAST} --cert', 'monotone'),
    'fast+partialordered': (f'{FAST} --partialordered --partialrepeat', 'monotone'),
    'fast+portcert_rank': (f'{FAST} --portcertrank rank', 'monotone'),
    'fast+capacity_packing': (f'{FAST} --capacityallocation packing', 'monotone'),
    'fast+certtyperank': (f'{FAST} --certtyperank', 'monotone'),
    'fast+strongbounds': (f'{FAST} --strongbounds', 'both'),
    'fast+closedcone': (f'{FAST} --closedcone', 'both'),
    'minimal': ('--minimal', 'both'),
}


def run_cli(n, terms, G, basis, flags, seconds, log=None, extra=''):
    edges = ','.join(f'{u}-{v}' for u, v in (tuple(i for i in range(n) if t >> i & 1) for t in terms))
    cmd = [sys.executable, CLI, '--n', str(n), '--edges', edges, '--size', str(G), '--workers', '1']
    cmd += (flags + ' ' + extra).split() + ([MONO] if basis == 'monotone' else [])
    if log:
        cmd += ['--log', log]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=seconds, cwd=ROOT)
    except subprocess.TimeoutExpired:
        return 'OPEN', None, time.time() - t0, 'timeout'
    out = p.stdout + p.stderr
    m = re.search(r'RESULT: (WITNESS|ALL UNSAT|STOPPED|MODEL FAILED VERIFICATION)', out)
    if p.returncode != 0 and not m:
        return 'ERROR', None, time.time() - t0, out[-400:]
    if not m:
        return 'ERROR', None, time.time() - t0, out[-400:]
    if m.group(1) == 'WITNESS':
        w = re.search(r'WITNESS verified=\w+: (\[.*\])', out)
        circ = [tuple(g) for g in json.loads(w.group(1).replace('(', '[').replace(')', ']'))] if w else None
        return 'SAT', circ, time.time() - t0, ''
    return {'ALL UNSAT': 'UNSAT', 'STOPPED': 'OPEN'}.get(m.group(1), 'BADWITNESS'), None, time.time() - t0, ''


def job(args):
    name, flags, n, terms, basis, G, expect, seconds, evidence = args
    extra = ' '.join(f'--minimal-evidence {e}' for e in evidence)
    verdict, circ, dt, info = run_cli(n, terms, G, basis, flags, seconds, extra=extra)
    if verdict == 'SAT':
        tt = ref.truth_table(n, terms)
        if circ is None or not ref.check_witness(n, tt, circ, (), True, basis):
            verdict = 'BADWITNESS'
    ok = None if verdict == 'OPEN' else verdict == expect
    return dict(config=name, flags=flags, n=n, terms=list(terms), basis=basis, G=G, expect=expect,
                verdict=verdict, ok=ok, seconds=round(dt, 2), info=info[-300:])


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--only', default='')
    ap.add_argument('--run', default=time.strftime('cli-%Y%m%d-%H%M%S'))
    ap.add_argument('--job-seconds', type=float, default=120)
    ap.add_argument('--max-n', type=int, default=5)
    a = ap.parse_args()
    t0 = time.time()
    cache = dif.load_ref_cache()
    only = set(a.only.split(',')) - {''}
    sets = {k: v for k, v in FLAGSETS.items() if not only or k in only}
    graphs = [(n, t) for kind, n, t in dif.instances(False) if kind == 'graph' and n <= a.max_n]
    evdir = tempfile.mkdtemp(prefix='cli_minimal_evidence_')
    jobs = []
    for n, t in graphs:
        for b in ('monotone', 'general'):
            r = cache.get((n, t, b))
            if not r or r['minimum'] is None:
                continue
            M = r['minimum']
            for name, (flags, bases) in sets.items():
                if bases != 'both' and bases != b:
                    continue
                if name == 'minimal':
                    ev = []
                    for G in (M - 1, M - 2):           # evidence produced by complete production runs
                        if G >= n - 1:
                            man = os.path.join(evdir, f'{n}_{"_".join(map(str, t))}_{b}_{G}.json')
                            v, _, _, _ = run_cli(n, t, G, b, '', a.job_seconds, extra=f'--manifest {man}')
                            if v == 'UNSAT':
                                ev.append(man)
                    jobs.append((name, flags, n, t, b, M, 'SAT', a.job_seconds, ev))
                    continue
                for G, expect in ((M - 1, 'UNSAT'), (M, 'SAT'), (M + 2, 'SAT')):
                    if G >= 1:
                        jobs.append((name, flags, n, t, b, G, expect, a.job_seconds, []))
    os.makedirs(dif.RESULTS, exist_ok=True)
    path = os.path.join(dif.RESULTS, f'{a.run}.jsonl')
    out = open(path, 'w', encoding='utf-8')
    out.write(json.dumps(dict(header=True, run=a.run, version=dif.source_version(), argv=sys.argv,
                              entry='cube_search.py main (subprocess)', jobs=len(jobs))) + '\n')
    print(f'{len(jobs)} CLI jobs on {len(graphs)} graphs, {len(sets)} flag sets', flush=True)
    bad, opened, done = [], 0, 0
    with ThreadPoolExecutor(a.workers) as ex:
        for f in as_completed([ex.submit(job, j) for j in jobs]):
            r = f.result()
            out.write(json.dumps(r) + '\n'); out.flush()
            done += 1
            if r['ok'] is None:
                opened += 1
            elif not r['ok']:
                bad.append(r)
                print('MISMATCH', json.dumps(r)[:400], flush=True)
            if done % 500 == 0:
                print(f'  {done}/{len(jobs)} ({time.time() - t0:.0f}s)', flush=True)
    print(f'DONE {done} CLI jobs, {len(bad)} mismatches, {opened} open (timeout {a.job_seconds}s) '
          f'({time.time() - t0:.0f}s)', flush=True)
