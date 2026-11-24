"""L-meta-1343, shard 2 of 3: is there a monotone circuit (AND/OR, fan-in two) with at most 21
gates for the edge function of the 11-vertex graph below, whose first three gates are
x6 OR x9, x7 OR x10 and their AND?  UNSAT = the range holds no such circuit.

Encoding: exactly G gates (wires n .. n+G-1), each AND or OR of two DIFFERENT earlier wires
(left < right), output = any gate wire. A smaller circuit pads with unused gates; a minimal
circuit has no copy or constant gates, so this covers every circuit of size <= G.
Rows: the edge inputs (must be 1) and the maximal independent sets (must be 0); for a
monotone circuit that is the same as agreeing on all 2^n inputs. Any model is re-checked on
all 2^n inputs anyway.
Symmetry breaking (sound): left < right; for two adjacent gates j, j+1 both after the seed,
if j+1 does not read j then (left_j, right_j) <= (left_{j+1}, right_{j+1}) lexicographically
(any circuit can be brought to this order by swapping adjacent independent gates past the seed).
Parallel: cubes on gate n+3 (the first free gate); each worker keeps one solver.

Usage: python mono_shard.py [--size 21] [--workers 11] [--log file]
"""
import argparse, itertools, os, sys, time, queue
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
sys.path.insert(0, r"C:\Users\Carson\Documents\ChatGPT\P=NP\.scratch-sat")
from multiprocessing import Pool
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc

N_IN = 11
EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10),
         (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
SEED = [(1, 6, 9), (1, 7, 10), (0, N_IN, N_IN + 1)]      # (op, left, right); op 0 = AND, 1 = OR


def target(x):
    return any(x >> u & 1 and x >> v & 1 for u, v in EDGES)


def rows():
    adj = {v: set() for v in range(N_IN)}
    for u, v in EDGES:
        adj[u].add(v); adj[v].add(u)
    mis = []
    for x in range(1 << N_IN):
        if target(x):
            continue
        if all(any(x >> u & 1 for u in adj[v]) for v in range(N_IN) if not x >> v & 1):
            mis.append(x)
    ones = [(1 << u) | (1 << v) for u, v in EDGES]
    return ones, mis


def evaluate(circ, out, x):
    v = [bool(x >> i & 1) for i in range(N_IN)]
    for op, l, r in circ:
        v.append(v[l] and v[r] if op == 0 else v[l] or v[r])
    return v[out]


def build(G, exact=False, distinct=False):
    """Left and right operands as separate one-hot choices (linear per row, not quadratic)."""
    n = N_IN; W = n + G
    pool = IDPool(); cl = []
    one = lambda xs: cl.extend(CardEnc.equals(xs, 1, vpool=pool).clauses)
    isand = {j: pool.id(('and', j)) for j in range(n, W)}
    sel = {j: [[pool.id(('s', j, k, i)) for i in range(j)] for k in range(2)] for j in range(n, W)}
    outv = {j: pool.id(('out', j)) for j in range(n, W)}
    for j in range(n, W):
        L, R = sel[j]
        one(L); one(R)
        for i in range(j):                      # left < right
            cl.extend([-L[i], -R[l]] for l in range(i + 1))
    one(list(outv.values()))
    for k, (op, l, r) in enumerate(SEED):
        j = n + k
        cl += [[sel[j][0][l]], [sel[j][1][r]], [isand[j]] if op == 0 else [-isand[j]]]
    first = n + len(SEED)
    for j in range(first, W - 1):               # colex order on (right, left) for adjacent gates
        L, R = sel[j]; L2, R2 = sel[j + 1]
        for i in range(j):
            cl.extend([-R[i], -R2[l]] for l in range(i))
            for l in range(i):
                cl.extend([-R[i], -R2[i], -L[l], -L2[k]] for k in range(l))
    if exact:   # output is the last gate; every gate after the seed except the output is read later
        cl.append([outv[W - 1]])
        for i in range(first, W - 1):
            cl.append([sel[j][k][i] for j in range(i + 1, W) for k in range(2)])
    ones, mis = rows()
    for x in ones + mis:
        v = {j: pool.id(('v', x, j)) for j in range(n, W)}
        for j in range(n, W):
            a = [pool.id(('a', x, j, k)) for k in range(2)]
            for k in range(2):
                for i, sv in enumerate(sel[j][k]):
                    if i < n:
                        cl.append([-sv, a[k]] if x >> i & 1 else [-sv, -a[k]])
                    else:
                        cl += [[-sv, -a[k], v[i]], [-sv, a[k], -v[i]]]
            f, A, B, g = v[j], a[0], a[1], isand[j]
            cl += [[-g, -f, A], [-g, -f, B], [-g, f, -A, -B],      # AND
                   [g, -f, A, B], [g, f, -A], [g, f, -B]]          # OR
        want = target(x)
        for j in range(n, W):
            cl.append([-outv[j], v[j]] if want else [-outv[j], -v[j]])
    if distinct:
        # Sound for this search: the rows are fixed and decide correctness, and each row is evaluated on
        # its own, so a gate that equals an earlier wire (or a constant) on every row can be replaced by it,
        # leaving an unused gate. With every gate used (exact mode) such circuits are never minimal.
        R = ones + mis
        V = lambda x, j: pool.id(('v', x, j))
        for j in range(first, W):
            cl.append([V(x, j) for x in R])                        # not constant 0 on the rows
            cl.append([-V(x, j) for x in R])                       # not constant 1 on the rows
            for i in range(n):                                     # not a copy of an input
                cl.append([-V(x, j) if x >> i & 1 else V(x, j) for x in R])
            for i in range(n, j):                                  # not a copy of an earlier gate
                ds = []
                for x in R:
                    d = pool.id(('d', i, j, x))
                    cl += [[-d, V(x, i), V(x, j)], [-d, -V(x, i), -V(x, j)]]
                    ds.append(d)
                cl.append(ds)
    return pool, cl, isand, sel, outv, first


_W = {}


def init(G, solver, exact, distinct=False):
    tg = os.environ.get('MONO_TEST_GRAPH')
    if tg:
        global N_IN, EDGES, SEED
        nn, es = tg.split(':')
        N_IN = int(nn); EDGES = [tuple(map(int, e.split('-'))) for e in es.split(',')]; SEED = []
    pool, cl, isand, sel, outv, first = build(G, exact, distinct)
    _W.update(s=Solver(name=solver, bootstrap_with=cl), isand=isand, sel=sel, outv=outv, first=first, G=G)


def run_cube(cube):
    op, l, r = cube
    w = _W; j = w['first']; t0 = time.time()
    assume = [w['sel'][j][0][l], w['sel'][j][1][r], w['isand'][j] if op == 0 else -w['isand'][j]]
    s = w['s']
    if not s.solve(assumptions=assume):
        return cube, 'UNSAT', None, time.time() - t0
    m = set(lit for lit in s.get_model() if lit > 0)
    circ = []
    for g in range(N_IN, N_IN + w['G']):
        lr = [next(i for i, v in enumerate(w['sel'][g][k]) if v in m) for k in range(2)]
        circ.append((0 if w['isand'][g] in m else 1, *lr))
    out = next(g for g, v in w['outv'].items() if v in m)
    return cube, 'MODEL', (circ, out), time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--size', type=int, default=21)
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--solver', default='maplechrono')
    ap.add_argument('--log', default=None)
    ap.add_argument('--exact', action='store_true',
                    help='every gate used and output last; run sizes min-size..size one by one')
    ap.add_argument('--min-size', type=int, default=4)
    ap.add_argument('--distinct', action='store_true',
                    help='exact mode only: no gate equals an earlier wire or a constant on the rows')
    ap.add_argument('--test-graph', default=None, help='testing only: n:u-v,u-v,... and no seed')
    a = ap.parse_args()
    if a.test_graph:
        global N_IN, EDGES, SEED
        nn, es = a.test_graph.split(':')
        N_IN = int(nn); EDGES = [tuple(map(int, e.split('-'))) for e in es.split(',')]; SEED = []
        os.environ['MONO_TEST_GRAPH'] = a.test_graph
    log = open(a.log, 'a', encoding='utf-8') if a.log else None

    def say(msg):
        line = f'{time.strftime("%H:%M:%S")} {msg}'
        print(line, flush=True)
        if log:
            log.write(line + '\n'); log.flush()

    ones, mis = rows()
    j = N_IN + len(SEED)
    cubes = [(op, l, r) for r in range(j) for l in range(r) for op in (0, 1)]
    sizes = range(a.min_size, a.size + 1) if a.exact else [a.size]
    say(f'L-meta-1343 shard 2: <= {a.size} gates, seed {SEED}; rows {len(ones)} edges + {len(mis)} '
        f'maximal independent sets; {len(cubes)} cubes on gate {j}, {a.workers} workers, {a.solver}; '
        f'{"exact sizes " + str(list(sizes)) + " (every gate used, output last)" if a.exact else "padded encoding"}')
    T0 = time.time(); final = 'ALL UNSAT'
    for G in sizes:
        t0 = time.time(); done = 0; result = 'UNSAT'
        with Pool(a.workers, initializer=init, initargs=(G, a.solver, a.exact, a.distinct and a.exact)) as p:
            for cube, status, wit, dt in p.imap_unordered(run_cube, cubes):
                done += 1
                say(f'size {G} [{done}/{len(cubes)}] cube {cube}: {status} in {dt:.0f}s (elapsed {time.time() - t0:.0f}s)')
                if status == 'MODEL':
                    circ, out = wit
                    ok = all(evaluate(circ, out, x) == target(x) for x in range(1 << N_IN))
                    say(f'MODEL verified on all {1 << N_IN} inputs = {ok}: gates {circ}, output wire {out}')
                    result = 'WITNESS' if ok else 'MODEL FAILED RECHECK (encoding bug)'
                    p.terminate(); break
            p.terminate()
        say(f'size {G}: {result} after {time.time() - t0:.0f}s')
        if result != 'UNSAT':
            final = f'{result} at size {G}'; break
    say(f'RESULT: {final} (<= {a.size} gates, shard 2) after {time.time() - T0:.0f}s')

if __name__ == '__main__':
    main()
