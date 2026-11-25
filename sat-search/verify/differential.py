"""Differential testing of cube_search rules against the independent reference (verify/reference.py).

For every instance (small graph and non-graph monotone functions, all inputs essential) and basis, the
reference gives the exact minimum M (exact-G model, every wire read). Each configuration (one rule with its
prerequisites, the --fast set, --fast plus one extra rule) is run through cube_search.run_cube over the
complete first-gate cube set (orbit-reduced when the configuration uses symmetry) at:
  G = M - 1 : must be UNSAT (a WITNESS that fails the reference check is an encoding bug);
  G = M     : must be SAT  (UNSAT = the configuration is unsound for minimum circuits);
  G = M + 1 : compared with the reference's exact-(M+1) verdict; a disagreement there marks the configuration
              as minimum-preserving only (it must not be combined with the 'exact G covers G-2' shortcut).
Pinned-prefix jobs take random prefixes (from reference witnesses and random gates), compute the reference
minimum M_P over circuits starting with that prefix, and require SAT at G = M_P with the prefix pinned the
way the shard drivers pin it (cube = gate 0, fixgates for the rest, colex ordering after the prefix).
--minimal runs only where its prerequisite holds (G - 1 and G - 2 UNSAT by the reference).

Every job is recorded (results/differential/<run>.jsonl) with the source version of cube_search.py.
Usage: python verify/differential.py [--quick] [--workers 11] [--only CONFIG,...] [--run NAME]"""
import argparse, hashlib, json, os, random, subprocess, sys, time, traceback
from itertools import combinations
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, ROOT)
import warnings
warnings.filterwarnings('ignore')
import networkx as nx
import reference as ref
import cube_search as cs

RESULTS = os.path.join(ROOT, 'results', 'differential')
REF_CACHE = os.path.join(ROOT, 'results', 'reference_minima.jsonl')


# ------------------------------------------------------------------ instances

def instances(quick=False):
    out = []
    for g in nx.graph_atlas_g():
        k = g.number_of_nodes()
        if 3 <= k <= (4 if quick else 5) and nx.is_connected(g) and g.number_of_edges() >= 2:
            out.append(('graph', k, ref.graph_terms(k, g.edges())))
    # non-graph monotone families: every 3-input monotone function with all inputs essential, sampled
    # 4-input antichains, 3-uniform hypergraphs on 4-5 inputs, thresholds
    rng = random.Random(7)
    seen = {(k, t) for _, k, t in out}

    def add(kind, k, terms):
        terms = ref.normalize_terms(k, terms)
        tt = ref.truth_table(k, terms)
        if len(ref.essential_inputs(k, tt)) == k and (k, terms) not in seen:
            seen.add((k, terms))
            out.append((kind, k, terms))
    for r in range(1, 8):
        for fam in combinations(range(1, 8), r):
            add('mono3', 3, fam)
    for _ in range(6 if quick else 25):
        add('mono4', 4, rng.sample(range(1, 16), rng.randint(2, 5)))
    for k in ((4,) if quick else (4, 5)):
        triples = [sum(1 << i for i in c) for c in combinations(range(k), 3)]
        for _ in range(3 if quick else 6):
            add('hyper3', k, rng.sample(triples, rng.randint(2, len(triples))))
    for k, t in ((4, 2), (4, 3), (5, 2), (5, 3), (5, 4))[: 2 if quick else 5]:
        add('threshold', k, [sum(1 << i for i in c) for c in combinations(range(k), t)])
    return out


def is_graph(terms):
    return all(t.bit_count() == 2 for t in terms)


# ------------------------------------------------------------------ configurations

def configs(terms_example=None):
    """name -> (bases, spec). spec: fanout, readonce, symmetry, flags, portcosts recipe, needs_graph."""
    C = {}

    def add(name, bases, flags=(), fanout=False, readonce=False, symmetry=False, ports=None, graph=False,
            extra=None):
        f = {k: True for k in flags}
        if extra:
            f.update(extra)
        C[name] = dict(bases=bases, flags=f, fanout=fanout, readonce=readonce, symmetry=symmetry,
                       ports=ports, graph=graph)
    both, mono = ('monotone', 'general'), ('monotone',)
    gen = ('general',)
    add('plain', both)
    add('symmetry', both, symmetry=True)
    add('units', both, ('units',))
    add('reuse', both, ('reuse',))
    add('sens', both, ('sens',), graph=True)
    add('fanout', both, fanout=True, graph=True)
    add('readonce', both, readonce=True)
    add('parity', gen, ('parity',), readonce=True)
    add('usens', both, ('usens',), readonce=True)
    add('closedcone', both, ('closedcone',), readonce=True, graph=True)
    add('bypass', both, ('bypass',), readonce=True, graph=True)
    add('outdec', both, ('outdec',), graph=True)
    add('bottleneck', both, ('bottleneck',), readonce=True)
    add('elim', both, ('elim',), graph=True)
    add('strongbounds', both, ('strongbounds',))
    add('elimbypass', both, ('elim', 'bypass', 'elimbypass'), readonce=True, graph=True)
    add('elimlink', both, ('elim', 'elimlink'), graph=True)
    add('readersens', both, ('readersens',))
    add('readerbudget', both, ('readerbudget',), readonce=True, graph=True)
    add('elimclosure', both, ('elim', 'elimclosure'), graph=True)
    add('signeddom', both, ('bypass', 'signeddom'), readonce=True, graph=True)
    add('recursivebounds', both, ('recursivebounds',))
    add('notbypass', gen, ('bypass', 'notbypass'), readonce=True, graph=True)
    add('recclosure', both, ('recursivebounds', 'recclosure'))
    add('identifybounds', both, ('recursivebounds', 'identifybounds'))
    add('fanoutelim', both, ('elim', 'elimclosure', 'fanoutelim'), readonce=True, graph=True)
    add('lostreader', both, ('elim', 'elimclosure', 'fanoutelim', 'lostreader'), readonce=True, graph=True)
    add('pairro', both, ('pairro',), readonce=True)
    add('colorbounds', both, ('recursivebounds', 'colorbounds'))
    add('colorbudget', both, ('colorbudget',), readonce=True)
    add('sharecolor', both, ('sharecolor',), readonce=True)
    add('activecolor', both, ('sharecolor', 'activecolor'), readonce=True)
    add('colorzero', both, ('sharecolor', 'colorzero'), readonce=True)
    add('isolatedcolor', both, ('sharecolor', 'isolatedcolor'), readonce=True)
    add('polaritydom', gen, ('bypass', 'parity', 'polaritydom'), readonce=True, graph=True)
    add('portbounds', both, ('recursivebounds',), ports=dict())
    add('formulaports', gen, ('recursivebounds',), ports=dict(formula=True, polarity=True))
    add('monoports', mono, ('recursivebounds',), ports=dict(mono=True, separation=True))
    add('orderedports', mono, ('recursivebounds', 'orderedports'), ports=dict(mono=True, separation=True))
    add('formulaports_mono', mono, ('recursivebounds', 'orderedports'),
        ports=dict(mono=True, separation=True, profile=True, formula=True, output=True))
    for lvl in cs.PORT_CERTIFICATE_LEVELS:
        add(f'portcert_{lvl}', mono, ('recursivebounds', 'orderedports'),
            ports=dict(mono=True, certificate_level=lvl))
    add('portcert_output', mono, ('recursivebounds', 'orderedports'),
        ports=dict(mono=True, certificate_level='rank', certificate_output=True))
    add('portproviders', mono, ('recursivebounds', 'orderedports'),
        ports=dict(mono=True, certificate_level='rank', provider_eligibility=True))
    add('cert', mono, ('cert',))
    add('typed', mono, ('typed',))
    add('frontier', mono, ('frontier',))
    add('partialordered', mono, ('partialordered',))
    add('partialrepeat', mono, ('partialrepeat',))
    add('partialmultiplicity', mono, ('partialmultiplicity',))
    add('partialempty', mono, ('partialmultiplicity', 'partialempty'))
    add('coupledprojections', mono, ('partialmultiplicity', 'coupledprojections'))
    add('matchinginterface', mono, ('matchinginterface',), graph=True)
    add('minimal', both, ('minimal',))
    add('signedregions', both, ('signedregions',))
    fast = ('sens', 'units', 'usens', 'bypass', 'elim', 'elimclosure', 'signeddom', 'recursivebounds', 'notbypass',
            'recclosure', 'identifybounds', 'fanoutelim', 'pairro', 'colorbounds', 'sharecolor', 'colorbudget')
    add('fast', both, fast, fanout=True, readonce=True, symmetry=True, graph=True)
    for name in ('cert', 'typed', 'frontier', 'partialordered', 'partialrepeat', 'partialmultiplicity', 'minimal',
                 'parity', 'closedcone', 'outdec', 'bottleneck', 'strongbounds', 'readersens', 'readerbudget',
                 'activecolor', 'colorzero', 'isolatedcolor', 'lostreader', 'elimlink', 'elimbypass', 'orderedports',
                 'portcert_rank', 'signedregions'):
        base = C[name]
        bases = tuple(b for b in base['bases'] if b in C['fast']['bases'])
        add(f'fast+{name}', bases, tuple(set(fast) | set(base['flags'])), fanout=True, readonce=True,
            symmetry=True, ports=base['ports'], graph=True)
    return C


# ------------------------------------------------------------------ reference cache

REF_SECONDS = 90      # per reference SAT call; an undecided minimum excludes the instance (recorded)


def reference_minimum(n, terms, basis, prefix=()):
    tt = ref.truth_table(n, terms)
    G, w = ref.minimum(n, tt, basis, prefix=tuple(prefix), Gmax=4 * n + len(prefix) + 2, seconds=REF_SECONDS)
    return G, w


def load_ref_cache():
    cache = {}
    if os.path.exists(REF_CACHE):
        for line in open(REF_CACHE, encoding='utf-8'):
            r = json.loads(line)
            cache[(r['n'], tuple(r['terms']), r['basis'])] = r
    return cache


def ref_job(args):
    n, terms, basis = args
    t0 = time.time()
    tt = ref.truth_table(n, terms)
    G, w = reference_minimum(n, terms, basis)
    if G == 'undecided':
        return dict(n=n, terms=list(terms), basis=basis, minimum=None, undecided=True, witness=None,
                    exact_above=None, seconds=round(time.time() - t0, 2), limit_seconds=REF_SECONDS)
    above = ref.sat_exists(n, tt, G + 1, basis, seconds=REF_SECONDS) if G is not None else (None, {})
    return dict(n=n, terms=list(terms), basis=basis, minimum=G, witness=w,
                exact_above=None if above[1].get('undecided') else above[0] is not None,
                seconds=round(time.time() - t0, 2))


# ------------------------------------------------------------------ running cube_search

def source_version():
    try:
        head = subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], cwd=ROOT, capture_output=True,
                              text=True).stdout.strip()
        dirty = subprocess.run(['git', 'status', '--porcelain', '--', 'cube_search.py', 'partial_ordered.py',
                                'port_certificates.py', 'provider_certificates.py', 'provider_capacity.py',
                                'monotone_interface.py'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    except OSError:
        head, dirty = '?', ''
    h = hashlib.sha256()
    for f in ('cube_search.py', 'partial_ordered.py', 'port_certificates.py', 'provider_certificates.py',
              'provider_capacity.py', 'monotone_interface.py'):
        p = os.path.join(ROOT, f)
        if os.path.exists(p):
            h.update(open(p, 'rb').read())
    return dict(git=head, dirty=bool(dirty), sources_sha256=h.hexdigest()[:16])


def build_flags(spec, n, terms, basis, G, prefix):
    flags = dict(spec['flags'])
    if basis == 'monotone':
        flags['nonot'] = True
    if flags.get('reuse') and flags.get('units'):
        flags.pop('units')
    if spec['ports'] is not None:
        flags['portcosts'] = cs.port_costs(terms, **spec['ports'])
    if prefix:
        flags['fixgates'] = [(i, *g) for i, g in enumerate(prefix[1:], 1)]
        flags['colex_from'] = len(prefix)
    return flags


def cube_search_verdict(n, terms, basis, G, spec, prefix=()):
    """Run every cube; returns (verdict, detail). verdict in SAT / UNSAT / BADWITNESS / STOPPED / ERROR."""
    masks = list(terms)
    tt = ref.truth_table(n, terms)
    flags = build_flags(spec, n, terms, basis, G, prefix)
    if prefix:
        cubes = [tuple(prefix[0])]
    else:
        cubes = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)]
        if basis == 'general':
            cubes += [(2, i, i) for i in range(n)]
        if spec['symmetry']:
            edges = [tuple(i for i in range(n) if t >> i & 1) for t in terms]
            auts = cs.automorphisms(n, edges)
            cubes = [c for c in cubes if cs.orbit_min(c, auts)]
    statuses = {}
    for c in cubes:
        _, st, circ, _, info = cs.run_cube((n, masks, G, 'maplechrono', c, spec['fanout'], spec['readonce'],
                                            dict(flags)))
        statuses[str(c)] = st
        if st == 'WITNESS':
            if not ref.check_witness(n, tt, [tuple(g) for g in circ], prefix, True, basis):
                return 'BADWITNESS', dict(cube=c, circuit=circ)
            return 'SAT', dict(cube=c, circuit=circ)
        if st not in ('UNSAT',):
            return st, dict(cube=c, info=str(info))
    return 'UNSAT', dict(cubes=len(cubes),
                         analytical=sum(1 for c in cubes if statuses[str(c)] == 'UNSAT'))


JOB_SECONDS = [None]   # per-job wall limit (--job-seconds); a stopped job is open, neither pass nor fail


def _set_limit(seconds):
    JOB_SECONDS[0] = seconds


def job(args):
    name, spec, n, terms, kind, basis, G, prefix, expect = args
    t0 = time.time()
    timer = stop = None
    if JOB_SECONDS[0]:
        # cube_search's solver watcher polls the module-level STOP path; a per-process path gives a per-job limit
        import tempfile, threading
        stop = os.path.join(tempfile.gettempdir(), f'cube_search_STOP_{os.getpid()}')
        cs.STOP = stop
        timer = threading.Timer(JOB_SECONDS[0], lambda: open(stop, 'w').close())
        timer.start()
    try:
        verdict, detail = cube_search_verdict(n, terms, basis, G, spec, prefix)
    except Exception as e:
        verdict, detail = 'ERROR', dict(error=f'{type(e).__name__}: {e}', trace=traceback.format_exc()[-600:])
    finally:
        if timer:
            timer.cancel()
            if os.path.exists(stop):
                os.remove(stop)
    ok = None if verdict == 'STOPPED' else verdict == expect
    # Out-of-contract input (a graph-only rule on a non-graph family): a crash is a missing contract check,
    # recorded separately; a wrong verdict there is still a mismatch (silent unsoundness).
    contract = bool(spec['graph']) and not is_graph(terms)
    return dict(config=name, kind=kind, contract=contract, n=n, terms=list(terms), basis=basis, G=G, prefix=[list(g) for g in prefix],
                expect=expect, verdict=verdict, ok=ok, detail=detail, seconds=round(time.time() - t0, 3))


def prefix_cases(n, terms, basis, witness, M, rng, count):
    """Prefixes from random topological orders of a minimum witness (reference SAT at M) and random gates."""
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
        relab = []
        for j in order:
            op, a, b = witness[j]
            a, b = (rl(a), rl(b)) if op == 2 else tuple(sorted((rl(a), rl(b))))
            relab.append((op, a, b))
        k = rng.randint(1, min(3, G - 1))
        out.append(tuple(relab[:k]))
    for _ in range(count):
        k = rng.randint(1, 3)
        p = []
        for j in range(k):
            b = rng.randrange(1, n + j)
            p.append((rng.choice((0, 1)), rng.randrange(b), b))
        out.append(tuple(p))
    return out


def redundant_prefixes(n, prefixes, rng):
    """Pinned prefixes that contain a redundant gate or an equivalent signal: a duplicated gate (same op and
    operands), an absorption gate op'(i, op(i, y)) = i, or an idempotent repeat op(i, op(i, y)) = op(i, y).
    Their completions are generally nonminimum, which is what these jobs exercise."""
    out = []
    for P in prefixes:
        k = len(P)
        binary = [(j, g) for j, g in enumerate(P) if g[0] != 2]
        if not binary:
            continue
        out.append(P + (P[-1],) if P[-1][0] != 2 else P)                     # duplicated gate
        j, (op, i, y) = rng.choice(binary)
        w = n + j
        out.append(P + ((1 - op, min(i, w), max(i, w)),))                     # absorption: equals wire i
        out.append(P + ((op, min(i, w), max(i, w)),))                         # idempotent: equals wire w
    return [Q for Q in out if len(Q) > len(set(Q)) or Q not in prefixes]


def prefix_min(args):
    """Reference minimum over circuits starting with the prefix (capped at M + 3); None if above the cap."""
    n, t, kind, b, P, M = args
    tt = ref.truth_table(n, t)
    for G in range(max(len(P), M), M + 4):
        w, info = ref.sat_exists(n, tt, G, b, P, seconds=REF_SECONDS)
        if info.get('undecided'):
            return None
        if w is not None:
            return (n, t, kind, b, P, G)
    return None


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true')
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--only', default='')
    ap.add_argument('--run', default=time.strftime('run-%Y%m%d-%H%M%S'))
    ap.add_argument('--prefixes', type=int, default=2, help='prefix cases per (instance, basis) of each type')
    ap.add_argument('--no-prefix', action='store_true')
    ap.add_argument('--no-whole', action='store_true', help='skip whole-function jobs (prefix jobs only)')
    ap.add_argument('--job-seconds', type=float, default=None, help='per-job wall limit; stopped jobs stay open')
    ap.add_argument('--resume', action='store_true', help='append to the run file, skipping recorded jobs')
    ap.add_argument('--points', choices=('base', 'padded'), default='base',
                    help='base: M-1, M, M+1 and prefix minima; padded: M+2, M+4 (SAT by padding), prefix '
                         'minima + 2 and + 4, and redundant-gate prefixes')
    a = ap.parse_args()
    t0 = time.time()
    os.makedirs(RESULTS, exist_ok=True)
    insts = instances(a.quick)
    C = configs()
    only = set(a.only.split(',')) - {''}
    if only:
        C = {k: v for k, v in C.items() if k in only}
    version = source_version()
    print(f'{len(insts)} instances, {len(C)} configurations, cube_search {version}', flush=True)

    # reference minima (cached; the cache records the reference code hash)
    refsha = hashlib.sha256(open(os.path.join(HERE, 'reference.py'), 'rb').read()).hexdigest()[:16]
    cache = {k: v for k, v in load_ref_cache().items() if v.get('reference_sha256') == refsha}
    need = [(n, t, b) for _, n, t in insts for b in ('monotone', 'general') if (n, t, b) not in cache]
    with Pool(a.workers) as p, open(REF_CACHE, 'a', encoding='utf-8') as f:
        for r in p.imap_unordered(ref_job, need):
            r['reference_sha256'] = refsha
            cache[(r['n'], tuple(r['terms']), r['basis'])] = r
            f.write(json.dumps(r) + '\n'); f.flush()
    undecided = sorted((n, t, b) for (n, t, b), r in cache.items() if r.get('undecided')
                       and any((n, t) == (m, u) for _, m, u in insts))
    print(f'reference minima ready ({len(need)} computed, {len(undecided)} undecided within {REF_SECONDS}s per '
          f'call and excluded: {undecided}; {time.time() - t0:.0f}s)', flush=True)

    # prefix cases with reference minima
    rng = random.Random(11)
    pref = []   # (n, terms, kind, basis, prefix, M_P)
    redundant = set()
    if not a.no_prefix:
        todo = []
        redundant = set()
        for kind, n, t in insts:
            for b in ('monotone', 'general'):
                r = cache[(n, t, b)]
                if r['minimum'] is None or r['minimum'] < 2:
                    continue
                cases = prefix_cases(n, t, b, [tuple(g) for g in r['witness']], r['minimum'], rng, a.prefixes)
                for P in cases:
                    todo.append((n, t, kind, b, P, r['minimum']))
                if a.points == 'padded':
                    for P in redundant_prefixes(n, cases[:a.prefixes], random.Random(hash((n, t, b)) & 0xffff)):
                        todo.append((n, t, kind, b, P, r['minimum']))
                        redundant.add((n, t, b, P))
        # reference prefix minima are cached too (keyed by reference hash, instance, basis, prefix, M)
        pcache_path = os.path.join(ROOT, 'results', 'reference_prefix_minima.jsonl')
        pkey = lambda n, t, b, P, M: json.dumps([refsha, n, list(t), b, [list(g) for g in P], M])
        pcache = {}
        if os.path.exists(pcache_path):
            for line in open(pcache_path, encoding='utf-8'):
                r = json.loads(line)
                pcache[r['key']] = r['prefix_minimum']
        need = [x for x in todo if pkey(x[0], x[1], x[3], x[4], x[5]) not in pcache]
        with Pool(a.workers) as p, open(pcache_path, 'a', encoding='utf-8') as f:
            for x, res in zip(need, p.imap(prefix_min, need)):
                k = pkey(x[0], x[1], x[3], x[4], x[5])
                pcache[k] = res[5] if res is not None else None
                f.write(json.dumps(dict(key=k, prefix_minimum=pcache[k])) + '\n'); f.flush()
        pref = [(n, t, kind, b, P, pcache[pkey(n, t, b, P, M)]) for n, t, kind, b, P, M in todo
                if pcache[pkey(n, t, b, P, M)] is not None]
        print(f'{len(pref)} prefix cases with a reference minimum ({time.time() - t0:.0f}s)', flush=True)
    jobs = []
    for n, t, kind, b, P, MP in pref:
        for name, spec in C.items():
            if b in spec['bases'] and not spec['flags'].get('minimal'):
                if a.points == 'base':
                    jobs.append((name, spec, n, t, kind, b, MP, P, 'SAT'))
                    if MP - 1 >= len(P):
                        jobs.append((name, spec, n, t, kind, b, MP - 1, P, 'UNSAT'))
                else:   # padding appends two gates at the end, so the prefix is kept (n >= 2)
                    if (n, t, b, P) in redundant:
                        jobs.append((name, spec, n, t, kind, b, MP, P, 'SAT'))
                        if MP - 1 >= len(P):
                            jobs.append((name, spec, n, t, kind, b, MP - 1, P, 'UNSAT'))
                    for extra in (2, 4):
                        jobs.append((name, spec, n, t, kind, b, MP + extra, P, 'SAT'))
    for kind, n, t in ([] if a.no_whole else insts):
        for b in ('monotone', 'general'):
            r = cache[(n, t, b)]
            M = r['minimum']
            if M is None:
                continue
            for name, spec in C.items():
                if b not in spec['bases']:
                    continue
                if spec['graph'] and not is_graph(t) and name != 'fast' and not name.startswith('fast+'):
                    pass   # graph-specific rules still run on non-graphs: crashes/unsoundness are findings
                if a.points == 'padded':
                    if not spec['flags'].get('minimal') and n >= 2:
                        for G in (M + 2, M + 4):
                            jobs.append((name, spec, n, t, kind, b, G, (), 'SAT'))
                    continue
                points = [(M - 1, 'UNSAT'), (M, 'SAT')]
                if r['exact_above'] is not None:
                    points.append((M + 1, 'SAT' if r['exact_above'] else 'UNSAT'))
                if spec['flags'].get('minimal'):
                    points = [(M - 1, 'UNSAT'), (M, 'SAT')]
                for G, expect in points:
                    if G >= 1:
                        jobs.append((name, spec, n, t, kind, b, G, (), expect))
    path = os.path.join(RESULTS, f'{a.run}.jsonl')
    jkey = lambda name, n, t, b, G, P: (name, n, tuple(t), b, G, tuple(tuple(g) for g in P))
    if a.resume and os.path.exists(path):
        recorded = set()
        for line in open(path, encoding='utf-8'):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if not r.get('header') and r.get('ok') is not None:
                recorded.add(jkey(r['config'], r['n'], r['terms'], r['basis'], r['G'], r['prefix']))
        before = len(jobs)
        jobs = [j for j in jobs if jkey(j[0], j[2], j[3], j[5], j[6], j[7]) not in recorded]
        print(f'resume: {before - len(jobs)} jobs already recorded', flush=True)
    print(f'{len(jobs)} jobs to run (whole-function and pinned-prefix)', flush=True)
    out = open(path, 'a' if a.resume else 'w', encoding='utf-8')
    out.write(json.dumps(dict(header=True, run=a.run, version=version, reference_sha256=refsha,
                              instances=len(insts), configs=sorted(C), argv=sys.argv, resume=a.resume,
                              job_seconds=a.job_seconds)) + '\n')
    bad = {}
    crashes = {}
    opened = {}
    done = 0
    with Pool(a.workers, initializer=_set_limit, initargs=(a.job_seconds,)) as p:
        for r in p.imap_unordered(job, jobs, chunksize=1):
            done += 1
            out.write(json.dumps(r) + '\n'); out.flush()
            if r['ok'] is None:
                opened[r['config']] = opened.get(r['config'], 0) + 1
            elif not r['ok'] and r['contract'] and r['verdict'] == 'ERROR':
                crashes[r['config']] = crashes.get(r['config'], 0) + 1
            elif not r['ok']:
                key = (r['config'], r['basis'], r['expect'], r['verdict'])
                bad.setdefault(key, []).append(r)
                if len(bad[key]) == 1:
                    print(f'MISMATCH {key}: n={r["n"]} terms={r["terms"]} G={r["G"]} {r["detail"]}', flush=True)
            if done % 2000 == 0:
                print(f'  {done}/{len(jobs)} ({time.time() - t0:.0f}s)', flush=True)
    out.close()
    print(f'DONE {done} jobs, {sum(len(v) for v in bad.values())} mismatches in {len(bad)} classes '
          f'({time.time() - t0:.0f}s)', flush=True)
    for key, v in sorted(bad.items()):
        print(f'  {key}: {len(v)}')
    print(f'contract crashes (graph-only configuration on a non-graph family): {crashes}')
    print(f'open (stopped at the {a.job_seconds}s job limit): {sum(opened.values())} {opened}')
