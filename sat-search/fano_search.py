"""L-meta-1023: an AND/OR gate list (fan-in two) with G gates whose 7 outputs (any wires) equal the
7 line-ORs of the Fano plane (lines {0,1,3}+w mod 7) on every input with 2 or 3 true points."""
import itertools, sys, time
sys.path.insert(0, r"C:\Users\Carson\Documents\ChatGPT\P=NP\.scratch-sat")
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc

N = 7
LINES = [sorted({(u + w) % 7 for u in (0, 1, 3)}) for w in range(7)]
ROWS = [x for x in range(1 << N) if bin(x).count('1') in (2, 3)]
want = lambda w, x: any(x >> v & 1 for v in LINES[w])


def build(G):
    W = N + G
    pool = IDPool(); cl = []
    one = lambda xs: cl.extend(CardEnc.equals(xs, 1, vpool=pool).clauses)
    isand = {j: pool.id(('and', j)) for j in range(N, W)}
    sel = {j: [[pool.id(('s', j, k, i)) for i in range(j)] for k in range(2)] for j in range(N, W)}
    out = {w: [pool.id(('o', w, i)) for i in range(W)] for w in range(7)}
    for j in range(N, W):
        L, R = sel[j]; one(L); one(R)
        for i in range(j):
            cl.extend([-L[i], -R[l]] for l in range(i + 1))      # left < right
    for w in range(7):
        one(out[w])
    for j in range(N, W - 1):                                     # colex order of adjacent gates
        L, R = sel[j]; L2, R2 = sel[j + 1]
        for i in range(j):
            cl.extend([-R[i], -R2[l]] for l in range(i))
            for l in range(i):
                cl.extend([-R[i], -R2[i], -L[l], -L2[k]] for k in range(l))
    for x in ROWS:
        v = {j: pool.id(('v', x, j)) for j in range(N, W)}
        val = lambda i: (True if x >> i & 1 else False) if i < N else v[i]
        for j in range(N, W):
            a = [pool.id(('a', x, j, k)) for k in range(2)]
            for k in range(2):
                for i, sv in enumerate(sel[j][k]):
                    if i < N:
                        cl.append([-sv, a[k]] if x >> i & 1 else [-sv, -a[k]])
                    else:
                        cl += [[-sv, -a[k], v[i]], [-sv, a[k], -v[i]]]
            f, A, B, g = v[j], a[0], a[1], isand[j]
            cl += [[-g, -f, A], [-g, -f, B], [-g, f, -A, -B], [g, -f, A, B], [g, f, -A], [g, f, -B]]
        for w in range(7):
            t = want(w, x)
            for i in range(W):
                if i < N:
                    if bool(x >> i & 1) != t:
                        cl.append([-out[w][i]])
                else:
                    cl.append([-out[w][i], v[i]] if t else [-out[w][i], -v[i]])
    return cl, isand, sel, out


def decode(m, G, isand, sel, out):
    W = N + G
    gates = [(0 if isand[j] in m else 1, *[next(i for i, q in enumerate(sel[j][k]) if q in m) for k in range(2)])
             for j in range(N, W)]
    outs = [next(i for i, q in enumerate(out[w]) if q in m) for w in range(7)]
    return gates, outs


def check(gates, outs):
    for x in ROWS:
        val = [bool(x >> i & 1) for i in range(N)]
        for op, l, r in gates:
            val.append(val[l] and val[r] if op == 0 else val[l] or val[r])
        if any(val[outs[w]] != want(w, x) for w in range(7)):
            return False
    return True


_S = {}


def init(G):
    cl, isand, sel, out = build(G)
    _S.update(s=Solver(name='maplechrono', bootstrap_with=cl), G=G, isand=isand, sel=sel, out=out)


def run(cube):
    # first gate: AND/OR of inputs 0 and 1 (the plane's symmetry is 2-transitive, and (0,1) is the
    # least pair in the gate order, so some canonical witness starts this way); split on gate 2
    (op, l, r), (op2, l2, r2) = cube; S = _S; t = time.time()
    a = [S['sel'][N][0][l], S['sel'][N][1][r], S['isand'][N] if op == 0 else -S['isand'][N],
         S['sel'][N + 1][0][l2], S['sel'][N + 1][1][r2], S['isand'][N + 1] if op2 == 0 else -S['isand'][N + 1]]
    if not S['s'].solve(assumptions=a):
        return cube, None, time.time() - t
    m = set(x for x in S['s'].get_model() if x > 0)
    return cube, decode(m, S['G'], S['isand'], S['sel'], S['out']), time.time() - t


def port(cfg):
    """Portfolio worker: one solver on the whole instance, first gate fixed to AND/OR(0,1), clauses shuffled."""
    import random
    G, solver, op, seed = cfg
    t = time.time()
    cl, isand, sel, out = build(G)
    cl = cl + [[sel[N][0][0]], [sel[N][1][1]], [isand[N]] if op == 0 else [-isand[N]]]
    random.Random(seed).shuffle(cl)
    with Solver(name=solver, bootstrap_with=cl) as s:
        if not s.solve():
            return cfg, None, time.time() - t
        m = set(x for x in s.get_model() if x > 0)
    return cfg, decode(m, G, isand, sel, out), time.time() - t


def portfolio(G):
    from multiprocessing import Pool
    solvers = ['cadical300', 'kissat404', 'cadical195', 'glucose42', 'maplechrono', 'lingeling',
               'cadical153', 'mergesat3', 'maplecm', 'minisat22', 'glucose4']
    cfgs = [(G, solvers[i % len(solvers)], i % 2, i) for i in range(11)]
    print(f'{time.strftime("%H:%M:%S")} {G} gates: portfolio of 11 ({", ".join(c[1] + ("/AND" if c[2] == 0 else "/OR") for c in cfgs)})', flush=True)
    t0 = time.time()
    with Pool(11) as p:
        for cfg, res, dt in p.imap_unordered(port, cfgs):
            print(f'{time.strftime("%H:%M:%S")} {cfg[1]} first gate {"AND" if cfg[2] == 0 else "OR"}(0,1): '
                  f'{"FOUND" if res else "UNSAT"} in {dt:.0f}s', flush=True)
            if res:
                print(f'{G} gates: FOUND verified={check(*res)} after {time.time() - t0:.0f}s', flush=True)
                print('gates', res[0]); print('outs', res[1])
                p.terminate(); return
        print(f'{G} gates: UNSAT (both first-gate cases) after {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__' and sys.argv[1:2] == ['--portfolio']:
    portfolio(int(sys.argv[2]))
    sys.exit(0)

if __name__ == '__main__':
    from multiprocessing import Pool
    cubes = [((op, 0, 1), (op2, l2, r2)) for op in (0, 1) for r2 in range(N + 1) for l2 in range(r2) for op2 in (0, 1)]
    for G in map(int, sys.argv[1:] or ['13']):
        t0 = time.time(); found = None
        print(f'{time.strftime("%H:%M:%S")} {G} gates: {len(cubes)} cubes (first gate on inputs 0,1; split on the second gate), 11 workers', flush=True)
        with Pool(11, initializer=init, initargs=(G,)) as p:
            for k, (cube, res, dt) in enumerate(p.imap_unordered(run, cubes), 1):
                print(f'{time.strftime("%H:%M:%S")} {G} gates [{k}/{len(cubes)}] first gate {cube}: '
                      f'{"FOUND" if res else "UNSAT"} in {dt:.0f}s', flush=True)
                if res:
                    found = res; p.terminate(); break
            p.terminate()
        if found:
            print(f'{G} gates: FOUND verified={check(*found)} after {time.time() - t0:.0f}s', flush=True)
            print('gates', found[0]); print('outs', found[1]); break
        print(f'{G} gates: UNSAT after {time.time() - t0:.0f}s', flush=True)
