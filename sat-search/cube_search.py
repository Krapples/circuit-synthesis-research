"""Parallel exact circuit search for graph functions ("both ends of some edge are true").

Same encoding as .scratch-sat/search_524.py, for any graph: exactly G gates of AND/OR/NOT
(fan-in <= 2), every wire used, symmetry breaking on operand order and neighbouring gates.
The search space is split by the first gate's (op, left, right); cubes run in a process pool.

Stop safely at any time by creating the file STOP next to this script: every worker interrupts
its solver within ~5 s and the run exits (no orphaned processes).

Usage: python cube_search.py --n 9 --edges 0-1,1-2,... --size 11 [--workers 11] [--log run.log]
"""
import argparse, itertools, os, sys, threading, time
from math import comb
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
sys.path.insert(0, r"C:\Users\Carson\Documents\ChatGPT\P=NP\.scratch-sat")
from multiprocessing import Pool
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc

HERE = os.path.dirname(os.path.abspath(__file__))
STOP = os.path.join(HERE, 'STOP')


def build(n, G, colex_from=0):
    """colex_from: apply the adjacent-gate ordering only from gate n + colex_from on (callers that pin the
    first gates, e.g. a shard seed, must not let the ordering constrain the pinned prefix)."""
    output = n - 1 + G
    pool = IDPool(); clauses = []
    ops = {j: [pool.id((j, op)) for op in ('and', 'or', 'not')] for j in range(n, output + 1)}
    select = {(j, k): [pool.id((j, k, i)) for i in range(j)] for j in ops for k in range(2)}
    one = lambda xs: clauses.extend(CardEnc.equals(xs, 1, vpool=pool).clauses)
    for j, (a, o, no) in ops.items():
        left, right = select[j, 0], select[j, 1]
        one([a, o, no]); one(left); one(right)
        for i in range(j):
            clauses.extend([-left[i], -right[l]] for l in range(i))
            clauses.extend([[-left[i], -right[i], no], [-no, -left[i], right[i]]])
            if i >= n:
                clauses.append([-no, -left[i], -ops[i][2]])
        if j == output or j < n + colex_from:
            continue
        nl, nr = select[j + 1, 0], select[j + 1, 1]
        for i in range(j):
            for l in range(i):
                clauses.append([-right[i], -nr[l]])
            for l in range(i):
                for k in range(l):
                    clauses.append([-right[i], -nr[i], -left[l], -nl[k]])
    for i in range(output):
        clauses.append([select[j, k][i] for j in range(max(n, i + 1), output + 1) for k in range(2)])
    # Implied bound, stated explicitly to help the solver: AND/OR read two different wires and NOT reads
    # one, while all n + G - 1 non-output wires must be read, so #NOT + extra fan-out = G - n + 1.
    bound = G - n + 1
    if bound < 0:
        clauses.append([])
    elif bound < G:
        clauses.extend(CardEnc.atmost([ops[j][2] for j in ops], bound=bound, vpool=pool).clauses)
    return output, pool, clauses, ops, select


def add_fanout_rules(n, masks, ops, select, clauses):
    """Graph-specific fan-out rules (sound with NOT gates too, since x_u enters only through that gate).
    AND(x_u, x_v) with x_u read nowhere else: when x_v = 0 the output ignores x_u, impossible if u has a
    neighbour other than v. OR(x_u, x_v) with x_u read nowhere else: when x_v = 1 the output ignores x_u,
    which needs v not adjacent to u and N(u) a subset of N(v). Otherwise x_u must be read by another gate."""
    nbr = [set() for _ in range(n)]
    for m in masks:
        u, v = [i for i in range(n) if m >> i & 1]
        nbr[u].add(v); nbr[v].add(u)
    for j, (a, o, no) in ops.items():
        left, right = select[j, 0], select[j, 1]
        elsewhere = [[select[h, k][i] for h in ops if h != j for k in range(2)] for i in range(n)]
        for v in range(n):
            for u in range(v):
                pick = [-left[u], -right[v]]
                for x, y in ((u, v), (v, u)):
                    if nbr[x] - {y}:
                        clauses.append([-a, *pick, *elsewhere[x]])
                    if y in nbr[x] or not nbr[x] <= nbr[y]:
                        clauses.append([-o, *pick, *elsewhere[x]])


def add_readonce_rules(n, G, masks, pool, ops, select, clauses, parity=False):
    """R_i = 'wire i is read by two or more gates', for every non-output wire.
    (a) Budget: AND/OR read two different wires, NOT one, every non-output wire is read, so
        excess fan-out = G - n + 1 - #NOT, and the number of repeated wires is at most that:
        sum R_i + #NOT <= G - n + 1.
    (b) Read-once obstructions: with no repeated wire the circuit is a formula; setting all inputs
        outside an induced triangle or induced 4-vertex path to 0 would leave a read-once formula
        (unate, so NOT gates do not help) for that subgraph's edge function, which is impossible.
        So one of its vertices, or some internal gate, is repeated."""
    output = n + G - 1
    R = {}
    for i in range(output):
        rep = pool.id(('repeat', i))
        R[i] = rep
        uses = []
        for j in range(max(n, i + 1), output + 1):
            l, r = select[j, 0][i], select[j, 1][i]
            u = pool.id(('uses', j, i))
            clauses.extend([[-l, u], [-r, u], [-u, l, r]])
            uses.append(u)
        for k, u in enumerate(uses):
            for v in uses[k + 1:]:
                clauses.append([-u, -v, rep])
            clauses.append([-rep, -u, *uses[:k], *uses[k + 1:]])
    lits = list(R.values()) + [ops[j][2] for j in ops]
    bound = G - n + 1
    if bound < 0:
        clauses.append([])
    elif bound < len(lits):
        clauses.extend(CardEnc.atmost(lits, bound=bound, vpool=pool).clauses)
    # M[i]: wire i has two or more paths to the output (occurs twice in the unfolded formula):
    # M[i] <=> R[i] or some reader j of i has M[j]; M[output] = 0. Every wire is read, so every wire
    # reaches the output. If no wire of an induced P4/triangle S has M, the S-dependent wires form a
    # tree and the rest become constants once inputs outside S are 0: a read-once formula, impossible.
    M = {i: pool.id(('multi', i)) for i in range(output + 1)}
    clauses.append([-M[output]])
    for i in range(output - 1, -1, -1):
        wit = [R[i]]
        for j in range(max(n, i + 1), output):
            u, t = pool.id(('uses', j, i)), pool.id(('mpath', i, j))
            clauses.extend([[-t, u], [-t, M[j]], [-u, -M[j], t]])
            wit.append(t)
        clauses.append([-M[i], *wit])
        clauses.extend([[-w, M[i]] for w in wit])
    E = {frozenset(i for i in range(n) if m >> i & 1) for m in masks}
    obstructions = 0
    for size in (3, 4):
        for S in itertools.combinations(range(n), size):
            deg = sorted(sum(frozenset((u, v)) in E for v in S if v != u) for u in S)
            nedges = sum(deg) // 2
            if (size == 3 and deg == [2, 2, 2]) or (size == 4 and deg == [1, 1, 2, 2] and nedges == 3):
                clauses.append([M[v] for v in S])
                obstructions += 1
    if parity:
        add_parity_rules(n, G, masks, pool, ops, clauses)
    return R, obstructions


def add_parity_rules(n, G, masks, pool, ops, clauses):
    """P[i]/Q[i]: wire i has a path to the output through an even/odd number of NOT gates. The target is
    increasing in every input it depends on, so every such input needs an even path (all-odd = antitone).
    One-directional witnesses suffice: P[i] => some t, t => (j reads i) and the right parity at j, down to
    P[output] = 1, Q[output] = 0, so a true P[v] always traces a real even path. Needs the ('uses', j, i)
    variables from add_readonce_rules."""
    output = n + G - 1
    P = {i: pool.id(('even', i)) for i in range(output + 1)}
    Q = {i: pool.id(('odd', i)) for i in range(output + 1)}
    clauses.extend([[P[output]], [-Q[output]]])
    for i in range(output - 1, -1, -1):
        pe, po = [], []
        for j in range(max(n, i + 1), output + 1):
            u, no = pool.id(('uses', j, i)), ops[j][2]
            for same, flip, lst, par in ((P, Q, pe, 0), (Q, P, po, 1)):
                t = pool.id(('par', i, j, par))
                clauses.extend([[-t, u], [-t, no, same[j]], [-t, -no, flip[j]]])
                lst.append(t)
        clauses.append([-P[i], *pe])
        clauses.append([-Q[i], *po])
    for v in range(n):
        if any(m >> v & 1 for m in masks):
            clauses.append([P[v]])


def usens_clauses(n, masks, rows, pool, ops, select):
    """Unique-reader sensitivity (needs R from add_readonce_rules). If input x is read by exactly one gate
    j (R[x] false): if j is AND, j must be 1 on every edge row containing x (it is 0 at x = 0 and the
    output must flip); if j is OR, j must be 0 on every maximal independent set row not containing x
    (adding x makes f = 1). Uses only rows already encoded."""
    target = lambda y: any(y & m == m for m in masks)
    mis = [y for y in rows if not target(y) and all(target(y | 1 << i) for i in range(n) if not y >> i & 1)]
    cl = []
    for x in range(n):
        Rx = pool.id(('repeat', x))
        ex = [m for m in masks if m >> x & 1]
        for j, (a, o, no) in ops.items():
            for k in range(2):
                sel = select[j, k][x]
                for m in ex:
                    cl.append([Rx, -sel, -a, pool.id(('val', m, j))])
                for y in mis:
                    if not y >> x & 1:
                        cl.append([Rx, -sel, -o, -pool.id(('val', y, j))])
    return cl


def graph_facts(n, masks):
    """Neighbourhoods, connectivity, twins, whether f is read-once (connected graph: iff complete bipartite,
    i.e. no induced P4 or triangle), and essential inputs of each restriction f|x=b (by truth table)."""
    nbr = [0] * n
    for m in masks:
        u, v = [i for i in range(n) if m >> i & 1]
        nbr[u] |= 1 << v; nbr[v] |= 1 << u
    seen, stack = 1, [0]
    while stack:
        u = stack.pop()
        for v in range(n):
            if nbr[u] >> v & 1 and not seen >> v & 1:
                seen |= 1 << v; stack.append(v)
    connected = seen == (1 << n) - 1
    twin_free = len(set(nbr)) == n
    E = {frozenset(i for i in range(n) if m >> i & 1) for m in masks}
    readonce_fn = True
    for size in (3, 4):
        for S in itertools.combinations(range(n), size):
            deg = sorted(sum(frozenset((a, b)) in E for b in S if b != a) for a in S)
            if (size == 3 and deg == [2, 2, 2]) or (size == 4 and deg == [1, 1, 2, 2] and sum(deg) == 6):
                readonce_fn = False
    f = lambda y: any(y & m == m for m in masks)
    ess = {}
    for x in range(n):
        for b in (0, 1):
            ess[x, b] = [y for y in range(n) if y != x and any(
                f(z | (b << x)) != f(z | (b << x) | (1 << y))
                for z in range(1 << n) if not (z >> x & 1) and not (z >> y & 1))]
    return dict(nbr=nbr, connected=connected, twin_free=twin_free, readonce_fn=readonce_fn, ess=ess)


def add_closedcone_rules(n, G, masks, pool, ops, select, clauses):
    """Closed-cone obstruction (needs --readonce for R and uses). D[j]: some proper ancestor of gate j is a
    repeated wire. If D[j] = 0, every wire in j's cone has one reader, so the cone's inputs S reach the
    output only through j and f = F(h(x_S), rest). For a monotone graph function this needs, when S has an
    edge, no edge leaving S, and when S is independent, identical neighbourhoods. In a connected, twin-free
    graph whose function is not read-once, no gate with |S| >= 2 can do that (S = V would make f = h or
    not h, read-once). Any AND/OR gate has |S| >= 2 when D = 0, so every non-output AND/OR gate has D = 1.
    One-directional witnesses: D[j] => some operand i with (R[i] or D[i])."""
    gf = graph_facts(n, masks)
    if not (gf['connected'] and gf['twin_free'] and not gf['readonce_fn']):
        return 0
    output = n + G - 1
    D = {j: pool.id(('anc_rep', j)) for j in ops}
    for j in ops:
        wit = []
        for i in range(j):
            w = pool.id(('anc_w', j, i))
            ri = pool.id(('repeat', i))
            clauses.append([-w, pool.id(('uses', j, i))])
            clauses.append([-w, ri] + ([D[i]] if i >= n else []))
            wit.append(w)
        clauses.append([-D[j], *wit])
        if j != output:
            clauses.append([ops[j][2], D[j]])          # AND/OR gate (not NOT) => D[j]
    return 1


def add_bypass_rules(n, G, masks, rows, pool, ops, select, clauses):
    """A[g][i]: wire i has a path to the output avoiding gate g (one-directional witnesses).
    (1) Controlling-value bypass: if gate g reads input x and is AND (x = 0 forces g = 0), OR (x = 1 forces
        g = 1) or NOT (constant either way), then every y essential in f|x=0 (resp. f|x=1, resp. either)
        needs a path avoiding g.
    (2) Dominator sensitivity: for rows a, b differing only in x with f(a) != f(b), every gate g either
        differs on a and b or x has a path avoiding g. Needs --readonce (uses) and the rows' val variables."""
    gf = graph_facts(n, masks)
    output = n + G - 1
    # Wires are topologically numbered and every wire reaches the output, so: a wire after g always avoids
    # g; g itself never does; nothing avoids the output; and a wire before g that is read by a gate after g
    # avoids g directly. Only reads into gates before g need recursive witnesses.
    A = {}
    for g in ops:
        for i in range(output + 1):
            A[g, i] = pool.id(('avoid', g, i))
        if g == output:
            clauses.extend([[-A[g, i]] for i in range(output + 1)])
            continue
        clauses.append([-A[g, g]])
        clauses.extend([[A[g, i]] for i in range(g + 1, output + 1)])
        for i in range(g):
            wit = []
            for j in range(max(n, i + 1), output + 1):
                if j == g:
                    continue
                u = pool.id(('uses', j, i))
                if j > g:
                    wit.append(u)
                else:
                    w = pool.id(('avw', g, i, j))
                    clauses.extend([[-w, u], [-w, A[g, j]]])
                    wit.append(w)
            clauses.append([-A[g, i], *wit])
    for g, (a, o, no) in ops.items():
        for x in range(n):
            reads = [select[g, 0][x], select[g, 1][x]]
            for y in gf['ess'][x, 0]:
                for sl in reads:
                    clauses.append([-sl, -a, A[g, y]])
            for y in gf['ess'][x, 1]:
                for sl in reads:
                    clauses.append([-sl, -o, A[g, y]])
            for y in set(gf['ess'][x, 0]) | set(gf['ess'][x, 1]):
                clauses.append([-select[g, 0][x], -no, A[g, y]])
    target = lambda z: any(z & m == m for m in masks)
    for za in rows:
        for x in range(n):
            if za >> x & 1:
                continue
            zb = za | 1 << x
            if zb not in rows or target(za) == target(zb):
                continue
            for g in ops:
                va, vb = pool.id(('val', za, g)), pool.id(('val', zb, g))
                clauses.extend([[A[g, x], va, vb], [A[g, x], -va, -vb]])


def p4_or_triangle(n, masks, keep):
    """Does the graph induced on vertex set `keep` contain an induced P4 or triangle (i.e. its edge function
    is not read-once)?"""
    E = {frozenset(i for i in range(n) if m >> i & 1) for m in masks}
    for size in (3, 4):
        for S in itertools.combinations(sorted(keep), size):
            deg = sorted(sum(frozenset((a, b)) in E for b in S if b != a) for a in S)
            if (size == 3 and deg == [2, 2, 2]) or (size == 4 and deg == [1, 1, 2, 2] and sum(deg) == 6):
                return True
    return False


def add_dep_vars(n, G, pool, ops, select, clauses):
    """Exact structural dependence: dep[j, v] <=> wire j depends on input v; depa[j, k, v] for operand k."""
    dep, depa = {}, {}
    for j in ops:
        for v in range(n):
            d = dep[j, v] = pool.id(('dep', j, v)); da = []
            for k in range(2):
                t = depa[j, k, v] = pool.id(('depa', j, k, v)); da.append(t)
                for i, sel in enumerate(select[j, k]):
                    if i < n:
                        clauses.append([-sel, t] if i == v else [-sel, -t])
                    else:
                        clauses.extend([[-sel, -t, dep[i, v]], [-sel, t, -dep[i, v]]])
            clauses.extend([[-d, *da], [-da[0], d], [-da[1], d]])
    return dep, depa


def add_outdec_rules(n, G, masks, pool, ops, select, clauses):
    """Output-gate decomposition. With L/R = 'the output's left/right operand depends on v', a vertex is
    exclusive-left (A), exclusive-right (B) or shared (S). Fixing S (and the rest) and looking at two or
    three vertices: an OR output cannot have an edge between A and B (h(u) or k(v) is never u AND v);
    an AND output cannot have a shared vertex with neighbours in A and in B (set it to 1), nor a cross edge
    A-B together with an edge inside A or inside B. NOT gates elsewhere do not matter (h, k arbitrary)."""
    out = n + G - 1
    dep, depa = add_dep_vars(n, G, pool, ops, select, clauses)
    a, o, no = ops[out]
    L = {v: depa[out, 0, v] for v in range(n)}
    R = {v: depa[out, 1, v] for v in range(n)}
    edges = [tuple(i for i in range(n) if m >> i & 1) for m in masks]
    nbr = {v: set() for v in range(n)}
    for u, v in edges:
        nbr[u].add(v); nbr[v].add(u)

    def exA(v):            # literals that are all false iff v is exclusive-left
        return [-L[v], R[v]]

    def exB(v):
        return [-R[v], L[v]]
    for u, v in edges:
        for x, y in ((u, v), (v, u)):
            clauses.append([-o, *exA(x), *exB(y)])
            for p, q in edges:
                clauses.append([-a, *exA(x), *exB(y), *exA(p), *exA(q)])
                clauses.append([-a, *exA(x), *exB(y), *exB(p), *exB(q)])
    for s0 in range(n):
        for x in nbr[s0]:
            for y in nbr[s0]:
                if x != y:
                    clauses.append([-a, -L[s0], -R[s0], *exA(x), *exB(y)])
    # Pairwise rule: fix every input except x, y to some z. If f restricted to (x, y) is x AND y for some z,
    # x and y cannot be on opposite exclusive sides of an OR output (h(x) or k(y) is never x and y); if it is
    # x OR y for some z, they cannot be on opposite exclusive sides of an AND output.
    T = [any(z & m == m for m in masks) for z in range(1 << n)]
    all_or, all_and = True, True
    for x, y in itertools.combinations(range(n), 2):
        bx, by = 1 << x, 1 << y
        has_and = has_or = False
        for z in range(1 << n):
            if z & (bx | by) or T[z] or not T[z | bx | by]:
                continue
            fx, fy = T[z | bx], T[z | by]
            has_and |= not fx and not fy
            has_or |= fx and fy
            if has_and and has_or:
                break
        all_or &= has_or; all_and &= has_and
        for u, v in ((x, y), (y, x)):
            if has_and:
                clauses.append([-o, *exA(u), *exB(v)])
            if has_or:
                clauses.append([-a, *exA(u), *exB(v)])
    # If every pair forbids splitting across an AND (resp. OR) output, such an output has an operand that
    # depends on every input (otherwise some u is exclusive-left and some v exclusive-right... or one side
    # misses an input that the other side has exclusively). One selector says which side.
    for flag, op in ((all_or, a), (all_and, o)):
        if flag:
            side = pool.id(('fullside', op))
            for v in range(n):
                clauses.extend([[-op, -side, L[v]], [-op, side, R[v]]])


def add_bottleneck_rules(n, G, masks, pool, ops, select, clauses, sizes=(2, 3)):
    """Information bottlenecks. For an input set S, call a wire pure if it depends only on S, and a boundary
    wire if it is pure and read by a non-pure gate (or is the output). The output equals F(boundary values,
    outside inputs), so 2^(#boundary) >= q(S), the number of distinct functions of the outside inputs
    obtained by fixing S (computed from the truth table). Pure is exact; boundary is one-directional."""
    out = n + G - 1
    f = lambda y: any(y & m == m for m in masks)
    count = 0
    for size in sizes:
        for S in itertools.combinations(range(n), size):
            Smask = sum(1 << v for v in S)
            outside = [v for v in range(n) if not Smask >> v & 1]
            funcs = set()
            for sub in range(1 << size):
                sa = sum(1 << S[k] for k in range(size) if sub >> k & 1)
                funcs.add(tuple(f(sa | sum(1 << outside[k] for k in range(len(outside)) if z >> k & 1))
                                for z in range(1 << len(outside))))
            need = (len(funcs) - 1).bit_length()
            if need <= 1:
                continue
            tag = ('bn', S)
            pure = {i: pool.id((tag, 'pure', i)) for i in ops}
            for j in ops:
                opp = []
                for k in range(2):
                    t = pool.id((tag, 'opp', j, k)); opp.append(t)
                    for i, sel in enumerate(select[j, k]):
                        if i < n:
                            clauses.append([-sel, t] if Smask >> i & 1 else [-sel, -t])
                        else:
                            clauses.extend([[-sel, -t, pure[i]], [-sel, t, -pure[i]]])
                clauses.extend([[-pure[j], opp[0]], [-pure[j], opp[1]], [pure[j], -opp[0], -opp[1]]])
            bvars = []
            for i in list(S) + list(ops):
                b = pool.id((tag, 'bd', i)); bvars.append(b)
                if i >= n:
                    clauses.append([-b, pure[i]])
                if i == out:
                    continue
                wit = []
                for j in range(max(n, i + 1), out + 1):
                    w = pool.id((tag, 'bw', i, j)); wit.append(w)
                    clauses.extend([[-w, pool.id(('uses', j, i))], [-w, -pure[j]]])
                clauses.append([-b, *wit])
            clauses.extend(CardEnc.atleast(bvars, bound=need, vpool=pool).clauses)
            count += 1
    return count


def binary_lb(n, T, fixed, deleted_graph_keep):
    """Lower bound on binary gates for g = f with inputs in `fixed` (dict v -> 0/1) fixed, from the truth
    table T of f. m = number of essential inputs.
    m - 1 always; m if g is not read-once (deleted_graph_keep() says the graph part has an induced P4 or
    triangle); m + 1 if g is persistent (fixing any essential input to 0 or 1 leaves every other essential
    input essential): the first binary gate of a binary-minimal circuit reads literals of two distinct
    inputs, each has a controlling value, so both inputs need another path out: two units of excess
    fan-out, and excess = B - m + 1. m + 2 if moreover setting any two essential inputs to 0 leaves an
    induced P4 or triangle: with excess exactly 2 both units sit on those two branches, every other input
    has a unique path, and setting the two to 0 would leave a read-once formula."""
    base = sum(b << v for v, b in fixed.items())
    free = [v for v in range(n) if v not in fixed]

    def ess(fx, y):
        b0 = base + sum(c << v for v, c in fx.items())
        others = [v for v in free if v not in fx and v != y]
        for k in range(1 << len(others)):
            z = b0 + sum(1 << others[t] for t in range(len(others)) if k >> t & 1)
            if T[z] != T[z | 1 << y]:
                return True
        return False
    E = [y for y in free if ess({}, y)]
    m = len(E)
    if m == 0:
        return 0
    lb = m - 1
    if not deleted_graph_keep(()):
        return lb
    lb = m
    persistent = all(ess({u: c}, w) for u in E for c in (0, 1) for w in E if w != u)
    if not persistent:
        return lb
    lb = m + 1
    if all(deleted_graph_keep((u, w)) for u, w in itertools.combinations(E, 2)):
        lb = m + 2
    return lb


def add_global_not_bound(n, G, masks, pool, ops, clauses):
    """#NOT <= G - LB(f), with LB the analytical binary-gate bound of f itself."""
    T = [any(z & m == m for m in masks) for z in range(1 << n)]
    keep = lambda dele: p4_or_triangle(n, masks, [v for v in range(n) if v not in dele])
    L = binary_lb(n, T, {}, keep)
    bound = G - L
    nots = [ops[j][2] for j in ops]
    if bound < 0:
        clauses.append([])
    elif bound < len(nots):
        clauses.extend(CardEnc.atmost(nots, bound=bound, vpool=pool).clauses)
    return L


def add_elim_rules(n, G, masks, pool, ops, select, clauses, strong=False, closure=False, recdepth=0,
                   fanoutelim=False, lostreader=False):
    """Restriction gate elimination. Fix x = b and propagate constants (one-directional flags: truth =>
    flag; extra flags only make the bound harder, so a valid circuit always survives). Every binary gate
    with a constant operand disappears. The restricted function has m essential inputs, so it needs at least
    m - 1 binary gates, and m if it is not read-once (its graph part has an induced P4 or triangle). Hence
    eliminated binary gates + #NOT <= G - L."""
    gf = graph_facts(n, masks)
    out = n + G - 1
    nbr = gf['nbr']
    for x in range(n):
        for b in (0, 1):
            m = len(gf['ess'][x, b])
            if m == 0:
                continue
            if b == 0:
                keep = [v for v in range(n) if v != x]
            else:
                keep = [v for v in range(n) if v != x and not nbr[x] >> v & 1]
            Lb = m if p4_or_triangle(n, masks, keep) else m - 1
            if strong:
                T = [any(z & mm == mm for mm in masks) for z in range(1 << n)]
                kp = (lambda kk: (lambda dele: p4_or_triangle(n, masks, [v for v in kk if v not in dele])))(keep)
                Lb = max(Lb, binary_lb(n, T, {x: b}, kp))
            if recdepth > 0:
                Lb = max(Lb, rec_lb(rterms_restrict(_anti(masks), x, b), recdepth - 1))
            # Closure: inputs that are inessential under x = b can also be fixed (to 0) without changing
            # the restricted function, so the same bound applies to the bigger restriction.
            fixed = {x: b}
            if closure:
                ess_set = set(gf['ess'][x, b])
                fixed.update({y: 0 for y in range(n) if y != x and y not in ess_set})
            tag = ('elc' if closure else 'el', x, b)
            C0 = {j: pool.id((tag, 'c0', j)) for j in ops}
            C1 = {j: pool.id((tag, 'c1', j)) for j in ops}
            clauses.extend([[-C0[out]], [-C1[out]]])         # the restricted target is not constant
            clauses.extend([[-C0[j], -C1[j]] for j in ops])
            E = []
            for j, (aa, oo, nn) in ops.items():
                o0 = [pool.id((tag, 'o0', j, k)) for k in range(2)]   # operand k forced 0
                o1 = [pool.id((tag, 'o1', j, k)) for k in range(2)]   # operand k forced 1
                for k in range(2):
                    for i, sel in enumerate(select[j, k]):
                        if i < n:
                            if i in fixed:
                                clauses.append([-sel, o1[k] if fixed[i] else o0[k]])
                        else:
                            clauses.extend([[-sel, -C0[i], o0[k]], [-sel, -C1[i], o1[k]]])
                clauses.extend([[-aa, -o0[0], C0[j]], [-aa, -o0[1], C0[j]], [-aa, -o1[0], -o1[1], C1[j]],
                                [-oo, -o1[0], C1[j]], [-oo, -o1[1], C1[j]], [-oo, -o0[0], -o0[1], C0[j]],
                                [-nn, -o1[0], C0[j]], [-nn, -o0[0], C1[j]]])
                e = pool.id((tag, 'e', j)); E.append(e)
                for k in range(2):
                    clauses.extend([[nn, -o0[k], e], [nn, -o1[k], e]])
            if fanoutelim and closure:
                # Sharing destroyed by the restriction: e = B - n_ess + 1 >= (Lb - m + 1) + lost excess on
                # constant wires, i.e. #NOT + (repeated wires forced constant) <= G - n_ess + m - Lb.
                n_ess = sum(1 for v in range(n) if any(mm >> v & 1 for mm in masks))
                lost = [pool.id(('repeat', i)) for i in fixed]
                for j in ops:
                    if j == out:
                        continue
                    t = pool.id((tag, 'lostrep', j)); lost.append(t)
                    rj = pool.id(('repeat', j))
                    clauses.extend([[-rj, -C0[j], t], [-rj, -C1[j], t]])
                if lostreader:
                    # A repeated wire with a reader that becomes constant loses at least one reader, i.e. one
                    # unit of excess (or all of it if it dies). One shared indicator per wire: no double count.
                    for i in range(out):
                        if i in fixed:
                            continue
                        ri = pool.id(('repeat', i))
                        if i >= n:
                            li = pool.id((tag, 'lostrep', i))
                        else:
                            li = pool.id((tag, 'lostin', i)); lost.append(li)
                        for g in range(max(n, i + 1), out):
                            u = pool.id(('uses', g, i))
                            clauses.extend([[-ri, -u, -C0[g], li], [-ri, -u, -C1[g], li]])
                fb = G - n_ess + m - Lb
                flits = lost + [ops[j][2] for j in ops]
                if fb < 0:
                    clauses.append([])
                elif fb < len(flits):
                    clauses.extend(CardEnc.atmost(flits, bound=fb, vpool=pool).clauses)
            bound = G - Lb
            lits = E + [ops[j][2] for j in ops]
            if bound < 0:
                clauses.append([])
            elif bound < len(lits):
                clauses.extend(CardEnc.atmost(lits, bound=bound, vpool=pool).clauses)


def elim_bound_table(n, masks):
    """Analytical binary-gate lower bound Lb for each restriction x = b (as used by --elim), m = 0 -> None."""
    gf = graph_facts(n, masks)
    nbr = gf['nbr']
    out = {}
    for x in range(n):
        for b in (0, 1):
            m = len(gf['ess'][x, b])
            if m == 0:
                out[x, b] = None
                continue
            keep = [v for v in range(n) if v != x and (b == 0 or not nbr[x] >> v & 1)]
            out[x, b] = m if p4_or_triangle(n, masks, keep) else m - 1
    return gf, out


def elimbypass_clauses(n, masks, pool, ops, closure=False):
    """If fixing x = b makes gate g constant (the --elim constant flags), every input y still essential in
    f|x=b needs a path avoiding g (the --bypass 'avoid' variables). Constant wires carry no information.
    Extra constant flags only add constraints, so a valid circuit (flags = true constants) survives."""
    gf, lb = elim_bound_table(n, masks)
    cl = []
    for (x, b), L in lb.items():
        if L is None:
            continue
        tag = ('elc' if closure else 'el', x, b)
        for y in gf['ess'][x, b]:
            for g in ops:
                av = pool.id(('avoid', g, y))
                cl += [[-pool.id((tag, 'c0', g)), av], [-pool.id((tag, 'c1', g)), av]]
    return cl


def elimlink_clauses(n, masks, rows, pool, ops):
    """Constant flags under x = b fix the gate's value on every encoded row with that bit."""
    gf, lb = elim_bound_table(n, masks)
    cl = []
    for z in rows:
        for v in range(n):
            b = z >> v & 1
            if lb.get((v, b)) is None:
                continue
            tag = ('el', v, b)
            for j in ops:
                f = pool.id(('val', z, j))
                cl += [[-pool.id((tag, 'c0', j)), -f], [-pool.id((tag, 'c1', j)), f]]
    return cl


def readersens_clauses(n, masks, rows, pool, ops, select):
    """If flipping input x changes f at row z, the earliest gate whose value changes reads x directly and
    its other operand is unchanged, so it is non-controlling at row z: some gate reading x is AND with the
    other operand 1, OR with the other operand 0, or NOT. Needs only row z."""
    target = lambda y: any(y & m == m for m in masks)
    cl = []
    for z in rows:
        for x in range(n):
            if target(z) == target(z ^ (1 << x)):
                continue
            wit = []
            for j, (a, o, no) in ops.items():
                t = pool.id(('rsens', z, x, j)); wit.append(t)
                l, r = select[j, 0][x], select[j, 1][x]
                vl, vr = pool.id(('arg', z, j, 0)), pool.id(('arg', z, j, 1))
                cl += [[-t, l, r], [-t, -a, -l, vr], [-t, -a, -r, vl], [-t, -o, -l, -vr], [-t, -o, -r, -vl]]
            cl.append(wit)
    return cl


def add_readerbudget(n, G, masks, pool, ops, clauses):
    """Every binary gate reading x disappears under x = 0 and under x = 1, so binary readers of x + #NOT
    <= G - max_b Lb(x, b)."""
    gf, lb = elim_bound_table(n, masks)
    nots = [ops[j][2] for j in ops]
    for x in range(n):
        Ls = [lb[x, b] for b in (0, 1) if lb[x, b] is not None]
        if not Ls:
            continue
        bound = G - max(Ls)
        readers = []
        for j in ops:
            t = pool.id(('breader', x, j)); readers.append(t)
            clauses.append([-pool.id(('uses', j, x)), ops[j][2], t])
        lits = readers + nots
        if bound < 0:
            clauses.append([])
        elif bound < len(lits):
            clauses.extend(CardEnc.atmost(lits, bound=bound, vpool=pool).clauses)


def signeddom_clauses(n, masks, rows, pool, ops):
    """If flipping x at row z changes f, every path from x crosses gate g (no 'avoid' path) and no gate
    after g (in index order) is a NOT, then the output is a monotone function of g's value with everything
    else unaffected by x, so it acts as the identity on g: g's value equals f(z). Needs --bypass."""
    gates = list(ops)
    N = {g: pool.id(('notafter', g)) for g in gates}
    cl = [[-N[gates[-1]]]]
    for g, h in zip(gates, gates[1:]):
        no = ops[h][2]
        cl += [[-N[g], N[h], no], [-N[h], N[g]], [-no, N[g]]]
    T = lambda y: any(y & m == m for m in masks)
    for z in rows:
        for x in range(n):
            if T(z) == T(z ^ (1 << x)):
                continue
            for g in gates[:-1]:
                v = pool.id(('val', z, g))
                cl.append([pool.id(('avoid', g, x)), N[g], v if T(z) else -v])
    return cl


# ---------- recursive analytical binary-gate lower bounds ----------
# A function is an antichain of minimal true sets (bitmasks), each of size 1 or 2 for graph functions and
# their restrictions; RTRUE is the constant 1, () the constant 0. B(f) = minimum number of binary gates
# (NOT gates free). Facts used, valid for every circuit computing f:
#  * fixing input x = b removes every binary gate reading x (or a NOT chain of x), and what is left computes
#    f|x=b, so B >= (binary readers of x) + B(f|x=b);
#  * the first binary gate reads literals of two distinct essential inputs x, y; if x stays essential under
#    the value of y that controls the gate, x needs a second binary reader;
#  * excess fan-out = B - m + 1 (every wire used); inputs that must be read twice use one unit each, and if
#    setting them to 0 still leaves a non-read-once function (induced P4 or triangle) one more is needed.
RTRUE = ('T',)


def _anti(terms):
    a = set(terms)
    return tuple(sorted(t for t in a if not any(u != t and (u & t) == u for u in a)))


def rterms_restrict(terms, x, b):
    if terms == RTRUE:
        return RTRUE
    bit = 1 << x
    if b:
        new = set()
        for t in terms:
            if t & bit:
                t2 = t & ~bit
                if t2 == 0:
                    return RTRUE
                new.add(t2)
            else:
                new.add(t)
    else:
        new = {t for t in terms if not t & bit}
    return _anti(new)


def rterms_support(terms):
    if terms == RTRUE:
        return 0
    sup = 0
    for t in terms:
        sup |= t
    return sup


_obs_cache = {}


def rterms_obstruction(terms):
    """Not read-once: the edge (2-element) part has an induced P4 or triangle (singletons are disjoint ORs)."""
    if terms == RTRUE:
        return False
    if terms in _obs_cache:
        return _obs_cache[terms]
    E = {t for t in terms if bin(t).count('1') == 2}
    verts = sorted({v for t in E for v in range(t.bit_length()) if t >> v & 1})
    res = False
    for size in (3, 4):
        for S in itertools.combinations(verts, size):
            deg = sorted(sum(((1 << a) | (1 << b)) in E for b in S if b != a) for a in S)
            if (size == 3 and deg == [2, 2, 2]) or (size == 4 and deg == [1, 1, 2, 2] and sum(deg) == 6):
                res = True
                break
        if res:
            break
    _obs_cache[terms] = res
    return res


_rec_cache = {}
REC_CLOSURE = [False]
COLOR_BOUNDS = [False]    # set by run_cube from --colorbounds
MONO = [False]            # monotone circuits (no NOT gates): set by run_cube when flags['nonot']
ORDERED = [False]         # --orderedports: use ordered terminal groups in the connection bound


def incompatible_pairs(terms):
    """Pairs {x, y} for which some restriction gives x AND y and another gives x OR y (graph-type antichain:
    singleton and edge terms). Only edges xy of non-singleton vertices qualify (x AND y needs the term xy);
    x OR y needs an independent set (avoiding singletons) that activates a neighbour of x and of y."""
    if terms == RTRUE:
        return []
    single = {t for t in terms if bin(t).count('1') == 1}
    sv = {t.bit_length() - 1 for t in single}
    E = [t for t in terms if bin(t).count('1') == 2]
    nb = {}
    for t in E:
        a, b = [v for v in range(t.bit_length()) if t >> v & 1]
        nb.setdefault(a, set()).add(b); nb.setdefault(b, set()).add(a)
    out = []
    for t in E:
        x, y = [v for v in range(t.bit_length()) if t >> v & 1]
        if x in sv or y in sv:
            continue
        A = [a for a in nb.get(x, ()) if a != y and a not in sv]
        Bn = [b for b in nb.get(y, ()) if b != x and b not in sv]
        if any(a == b or b not in nb.get(a, ()) for a in A for b in Bn):
            out.append((x, y))
    return out


_chi_cache = {}


def chromatic(vertices, pairs):
    """Exact chromatic number of the graph on `vertices` with edge list `pairs` (small graphs)."""
    V = sorted(vertices)
    key = (tuple(V), tuple(sorted(pairs)))
    if key in _chi_cache:
        return _chi_cache[key]
    adj = {v: set() for v in V}
    for a, b in pairs:
        if a in adj and b in adj:
            adj[a].add(b); adj[b].add(a)
    order = sorted(V, key=lambda v: -len(adj[v]))
    if not V:
        return 0

    def ok(k):
        col = {}

        def bt(i):
            if i == len(order):
                return True
            v = order[i]
            used = {col[u] for u in adj[v] if u in col}
            for c in range(k):
                if c not in used and (c <= max(col.values(), default=-1) + 1):
                    col[v] = c
                    if bt(i + 1):
                        return True
                    del col[v]
            return False
        return bt(0)
    k = 1
    while not ok(k):
        k += 1
    _chi_cache[key] = k
    return k     # set by run_cube from the --recclosure flag (per worker process)


def rec_lb(terms, depth):
    if terms == RTRUE or not terms:
        return 0
    key = (terms, depth, REC_CLOSURE[0], COLOR_BOUNDS[0], MONO[0])
    if key in _rec_cache:
        return _rec_cache[key]
    sup = rterms_support(terms)
    V = [v for v in range(sup.bit_length()) if sup >> v & 1]
    m = len(V)
    if m <= 1:
        return 0
    base = m if rterms_obstruction(terms) else m - 1
    if COLOR_BOUNDS[0]:
        # First-shared-wire colouring: inputs sharing a first repeated wire (or the output) are pairwise
        # compatible, so repeated wires >= chi(J) - 1 and B >= m + chi(J) - 2.
        base = max(base, m + chromatic(V, incompatible_pairs(terms)) - 2)
    if depth <= 0:
        _rec_cache[key] = base
        return base
    if REC_CLOSURE[0]:
        # Restriction closure: excess fan-out e = B - m + 1 must cover the restricted function's need
        # L - k + 1 (k = its essential inputs), so B >= L(f|rho) + m - k for any nonconstant restriction.
        for v in V:
            for b in (0, 1):
                t = rterms_restrict(terms, v, b)
                k = bin(rterms_support(t)).count('1')
                if k:
                    base = max(base, rec_lb(t, depth - 1) + m - k)
    best = None
    for x, y in itertools.combinations(V, 2):
        if MONO[0]:
            # Monotone: the first gate reads x, y directly (no NOT), so only its own controlling value
            # matters (AND: 0, OR: 1); the gate type is unknown, so take the weaker of the two.
            c = min(_pair_bound(terms, x, y, 0, depth, m), _pair_bound(terms, x, y, 1, depth, m))
        else:
            c = _pair_bound(terms, x, y, None, depth, m)
        best = c if best is None else min(best, c)
        if best <= base:
            break
    res = max(base, best)
    _rec_cache[key] = res
    return res


def _pair_bound(terms, x, y, control, depth, m):
    """Bound given that the first binary gate reads x and y. control = None: unknown literal polarity
    (x must be essential under both values of y); control = c: the gate reads x, y directly with
    controlling value c (AND: 0, OR: 1)."""
    def stays(u, w):           # u still essential after fixing w to the controlling value(s)
        vals = (0, 1) if control is None else (control,)
        return all(rterms_support(rterms_restrict(terms, w, c)) >> u & 1 for c in vals)
    rx, ry = stays(x, y), stays(y, x)
    Lx = max(rec_lb(rterms_restrict(terms, x, b), depth - 1) for b in (0, 1))
    Ly = max(rec_lb(rterms_restrict(terms, y, b), depth - 1) for b in (0, 1))
    rem = terms
    if rx:
        rem = rterms_restrict(rem, x, 0)
    if ry:
        rem = rterms_restrict(rem, y, 0)
    topo = m - 1 + int(rx) + int(ry) + int(rterms_obstruction(rem))
    best = max(Lx + 1 + int(rx), Ly + 1 + int(ry), topo)
    if COLOR_BOUNDS[0]:
        # Forced-repeated inputs are their own first shared wires, unreachable by other inputs.
        H = {u for u, r in ((x, rx), (y, ry)) if r}
        sup = rterms_support(terms)
        rest = [v for v in range(sup.bit_length()) if sup >> v & 1 and v not in H]
        J = incompatible_pairs(terms)
        best = max(best, m - 1 + len(H) + max(0, chromatic(rest, [p_ for p_ in J if p_[0] not in H and p_[1] not in H]) - 1))
    if REC_CLOSURE[0]:
        # Closure with the forced repeats: a forced-repeated input that becomes inessential (or fixed)
        # also loses its unit of excess fan-out: B >= L(f|rho) + m - k + |H \ supp(f|rho)|.
        H = [u for u, r in ((x, rx), (y, ry)) if r]
        rs = [(rterms_restrict(terms, v, b), depth - 1) for v in (x, y) for b in (0, 1)]
        rs += [(rterms_restrict(rterms_restrict(terms, x, b), y, c), depth - 2) for b in (0, 1) for c in (0, 1)]
        for t, d in rs:
            sup_t = rterms_support(t)
            k = bin(sup_t).count('1')
            if k:
                lost = sum(1 for u in H if not sup_t >> u & 1)
                best = max(best, rec_lb(t, max(0, d)) + m - k + lost)
    return best


def identify_equal(terms, x, y):
    """f with x := y (antichain contraction of x into y)."""
    bx, by = 1 << x, 1 << y
    return _anti((t & ~bx) | by if t & bx else t for t in terms)


def terms_imply(a, b):
    """Does monotone function a imply b (a <= b)?"""
    if b == RTRUE or not a:
        return True
    if a == RTRUE:
        return False
    return all(any((u & t) == u for u in b) for t in a)


def complementary_lb(terms, x, y, depth):
    """Lower bound on binary gates of h(t, z) = f(x = t, y = not t, z). Its cofactors h0 = f|x=0,y=1 and
    h1 = f|x=1,y=0 are graph-type functions. m counts t (essential iff h0 != h1) plus the other inputs.
    Non-unate in t (neither cofactor implies the other) means not read-once, so >= m; restricting t gives
    a cofactor, so B >= L(cofactor) + m - k by the excess argument."""
    h0 = rterms_restrict(rterms_restrict(terms, x, 0), y, 1)
    h1 = rterms_restrict(rterms_restrict(terms, x, 1), y, 0)
    s0, s1 = rterms_support(h0), rterms_support(h1)
    m = bin(s0 | s1).count('1') + int(h0 != h1)
    L = max(0, m - 1)
    if not terms_imply(h0, h1) and not terms_imply(h1, h0):
        L = max(L, m)
    for t in (h0, h1):
        k = bin(rterms_support(t)).count('1')
        if k:
            L = max(L, rec_lb(t, max(0, depth - 1)) + m - k)
    return L


def _width_height(funcs):
    """funcs: list of antichains (monotone functions as minimal-term sets). Order: g <= h iff g implies h.
    Returns (width = largest antichain via Dilworth / bipartite matching, height = longest chain)."""
    k = len(funcs)
    le = [[i != j and terms_imply(funcs[i], funcs[j]) for j in range(k)] for i in range(k)]
    match = [-1] * k

    def aug(u, seen):
        for v in range(k):
            if le[u][v] and not seen[v]:
                seen[v] = True
                if match[v] < 0 or aug(match[v], seen):
                    match[v] = u
                    return True
        return False
    mm = sum(aug(u, [False] * k) for u in range(k))
    order = sorted(range(k), key=lambda i: sum(le[j][i] for j in range(k)))
    longest = {}
    for i in order:
        longest[i] = 1 + max((longest[j] for j in range(k) if le[j][i] and j in longest), default=0)
    return k - mm, max(longest.values(), default=0)


def _sperner_min(w):
    p = 0
    while comb(p, p // 2) < w:
        p += 1
    return p


def port_contexts(terms, Smask):
    """Non-constant restrictions of f to S, keyed by the assignment z of S's outside neighbours (all other
    outside inputs 0): {z: antichain over S}. Non-constant contexts form a convex set of z."""
    nbS = 0
    for t in terms:
        if t & Smask:
            nbS |= t & ~Smask
    ctx = {}
    z = nbS
    while True:
        if not any((t & Smask) == 0 and (t & ~z) == 0 for t in terms):
            surv = [t & Smask for t in terms if (t & ~Smask & ~z) == 0 and t & Smask]
            if surv:
                ctx[z] = _anti(surv)
        if z == 0:
            break
        z = (z - 1) & nbS
    return ctx


def chain_distinct(ctx):
    """Max number of distinct restricted functions along an increasing chain of outside assignments,
    walked in single-bit steps inside the (convex) set of non-constant contexts."""
    best = {}
    for z in sorted(ctx, key=lambda q: bin(q).count('1')):
        b = 1
        y = z
        while y:
            bit = y & -y
            pz = z & ~bit
            if pz in best:
                b = max(b, best[pz] + (ctx[pz] != ctx[z]))
            y &= y - 1
        best[z] = b
    return max(best.values(), default=0)


def separation_clique(ctx, limit=12):
    """Monotone ports: a required separation (a, b) has f_a not <= f_b, so some port is 1 at a and 0 at b.
    One monotone port cannot serve (a, b) and (c, d) if a <= d or c <= b. Ports >= clique number of this
    conflict graph (greedy clique, a valid lower bound)."""
    zs = list(ctx)
    seps = [(a, b) for a in zs for b in zs if a != b and not terms_imply(ctx[a], ctx[b])]
    if not seps:
        return 0
    sub = lambda u, v: (u & ~v) == 0
    conflict = lambda s1, s2: sub(s1[0], s2[1]) or sub(s2[0], s1[1])
    best = 1
    for start in seps[:200]:
        clique = [start]
        for t in seps:
            if t is not start and all(conflict(t, c) for c in clique):
                clique.append(t)
                if len(clique) >= limit:
                    break
        best = max(best, len(clique))
    return best


class PortCosts(dict):
    """Port-cost table {S: p(S)} with metadata: mono = valid only for monotone (NOT-free) circuits;
    pout = output-region costs (or None); fp = content fingerprint (safe cache key)."""
    def __init__(self, d, mono=False, pout=None):
        super().__init__(d)
        self.mono, self.pout = mono, pout
        self.fp = hash((tuple(sorted(d.items())), mono, tuple(sorted(pout.items())) if pout else None))


_FZERO, _FONE, _FINF = (), (0,), 10 ** 6
_fdp_cache = {}


def _fanti(it):
    a = set(it)
    if 0 in a:
        return _FONE
    return tuple(sorted(t for t in a if not any(u != t and (u & t) == u for u in a)))


def formula_dp(U, F):
    """Exact relaxed regional formula cost (monotone): least number of configurable ports such that a formula
    reading each variable of U once plus ports can realize every function in the family F (antichains over U;
    () = 0, (0,) = 1). Port-only subtrees collapse to one port, so the formula is a binary tree over U with AND
    controls (force 0 / pass) and OR controls (force 1 / pass). AND factors are forced (other side := 1), OR
    factors too (other side := 0); a gate's controlling constant may come from either child."""
    F = tuple(sorted(set(F)))
    if not F:
        return 0
    key = (U, F)
    if key in _fdp_cache:
        return _fdp_cache[key]
    if bin(U).count('1') == 1:
        if any(f not in (_FZERO, _FONE, (U,)) for f in F):
            res = _FINF
        else:
            res = len(set(F) - {(U,)})
        _fdp_cache[key] = res
        return res
    best = _FINF
    for c in (_FZERO, _FONE):
        if c in F:
            best = min(best, 1 + formula_dp(U, tuple(f for f in F if f != c)))
    low = U & -U
    L = (U - 1) & U
    while L:
        if L & low:
            R = U ^ L
            for op in (0, 1):
                kill = _FZERO if op == 0 else _FONE
                A, B, ok = set(), set(), True
                for f in F:
                    if f == kill:
                        continue
                    if op == 0:
                        a, b = _fanti(t & L for t in f), _fanti(t & R for t in f)
                        comb_ = _fanti(x | y for x in a for y in b)
                    else:
                        a, b = tuple(t for t in f if not t & ~L), tuple(t for t in f if not t & ~R)
                        comb_ = _fanti(a + b)
                    if comb_ != f:
                        ok = False
                        break
                    A.add(a); B.add(b)
                if ok:
                    for side in ((0, 1) if kill in F else (-1,)):
                        aa = A | ({kill} if side == 0 else set())
                        bb = B | ({kill} if side == 1 else set())
                        best = min(best, formula_dp(L, tuple(aa)) + formula_dp(R, tuple(bb)))
        L = (L - 1) & U
    _fdp_cache[key] = best
    return best


def _dual_terms(f):
    """Dual of a monotone function given as an antichain (minimal transversals); 0 <-> 1."""
    if f == _FZERO:
        return _FONE
    if f == _FONE:
        return _FZERO
    cur = {0}
    for t in f:
        nxt = set()
        for h in cur:
            if h & t:
                nxt.add(h)
            else:
                b = t
                while b:
                    lb = b & -b
                    nxt.add(h | lb)
                    b ^= lb
        cur = set(_fanti(nxt))
    return _fanti(cur)


def polarity_formula_cost(Smask, sigs):
    """formula_dp for circuits WITH free NOT gates. Push NOTs to the leaves (negation normal form, same binary
    count). Read once, each input of S is a literal of one sign. In a context with restricted function g
    (monotone, non-constant), the region's terminal is g or NOT g (downstream is id / NOT / const), so all
    essential inputs of g share a sign: positive -> the formula computes g; negative -> substituting y = NOT x
    the formula computes the dual g^d(y). Signs are constant on components of the co-essentiality graph;
    flipping all signs swaps AND/OR (same cost), so 2^(c-1) sign choices. Returns the minimum cost."""
    funcs = list(sigs)
    ess = []
    for g in funcs:
        m = 0
        for t in g:
            m |= t
        ess.append(m)
    comps = []
    for m in ess:
        if not m:
            continue
        merged = m
        keep = []
        for c in comps:
            if c & merged:
                merged |= c
            else:
                keep.append(c)
        comps = keep + [merged]
    best = _FINF
    for sign in range(1 << max(0, len(comps) - 1)):
        neg = 0
        for i, c in enumerate(comps[1:]):
            if sign >> i & 1:
                neg |= c
        fam = tuple(_dual_terms(g) if (m & neg) else g for g, m in zip(funcs, ess))
        best = min(best, formula_dp(Smask, fam))
        if best <= 1:
            break
    return best


def output_family(terms, Smask):
    """All restrictions the output region must realize on S: the non-constant ones, plus constant 0 if some
    context makes f identically 0 (no term inside S), plus constant 1 if a term lies entirely outside S."""
    F = set(port_contexts(terms, Smask).values())
    if not any(t & ~Smask == 0 for t in terms):
        F.add(_FZERO)
    if any(t & Smask == 0 for t in terms):
        F.add(_FONE)
    return F


def profile_ports(terms, Smask, ctx):
    """Activation-profile bound for an independent group S. Each non-constant restriction to S is an OR of the
    active vertices A(z). If every pair of S is active together in some context, every branching gate of the
    region's formula is an OR, so the AND gates that switch inputs on and off form a laminar family of
    controls; inputs behind the same controls have the same activation profile (set of contexts where they
    are active), and each control needs an incoming port. So ports >= number of distinct profiles, not
    counting "always active". (Holds with free NOT gates after normalising literal polarities.)"""
    V = [v for v in range(Smask.bit_length()) if Smask >> v & 1]
    if len(V) < 2 or not ctx:
        return 0
    act = {}
    for z, sig in ctx.items():
        if any(bin(t).count('1') != 1 for t in sig):
            return 0                         # S not independent here: not an OR of singletons
        act[z] = {t.bit_length() - 1 for t in sig}
    for x, y in itertools.combinations(V, 2):
        if not any(x in a and y in a for a in act.values()):
            return 0
    profiles = {frozenset(z for z, a in act.items() if x in a) for x in V}
    allz = frozenset(act)
    return len(profiles - {allz})


def port_costs(terms, mono=False, separation=False, profile=False, formula=False, output=False, polarity=False):
    """For every set S of inputs that is independent in the incompatibility graph J: p(S) = ceil(log2 q*(S)),
    q*(S) = number of distinct non-constant functions of S obtained by fixing all other inputs. Only outside
    neighbours of S matter (other outside inputs either make f constant 1 or do nothing)."""
    sup = rterms_support(terms)
    J = [(1 << x) | (1 << y) for x, y in incompatible_pairs(terms)]
    costs = {}
    Smask = sup
    while Smask:
        if not any(Smask & e == e for e in J):
            nbS = 0
            for t in terms:
                if t & Smask:
                    nbS |= t & ~Smask
            sigs = set()
            z = nbS
            while True:
                if not any(t & ~Smask == t and False for t in terms):
                    if not any((t & Smask) == 0 and (t & ~z) == 0 for t in terms):   # outside term on: f = 1
                        surv = [t & Smask for t in terms if (t & ~Smask & ~z) == 0 and t & Smask]
                        if surv:
                            sigs.add(_anti(surv))
                if z == 0:
                    break
                z = (z - 1) & nbS
            cost = (max(1, len(sigs)) - 1).bit_length()
            if profile and len(sigs) > 1:
                cost = max(cost, profile_ports(terms, Smask, port_contexts(terms, Smask)))
            if formula and len(sigs) > 1:
                fc = polarity_formula_cost(Smask, sigs) if polarity else formula_dp(Smask, tuple(sigs))
                if fc < _FINF:
                    cost = max(cost, fc)
            if mono and len(sigs) > 1:
                # Monotone circuits: the region is a monotone function of its incoming wires, which are
                # monotone in the outside inputs. Incomparable restricted functions need incomparable
                # incoming patterns (Sperner). A chain bound needs an actual increasing chain of outside
                # assignments (comparable functions alone do not force comparable patterns).
                w, _h = _width_height(list(sigs))
                ctx = port_contexts(terms, Smask)
                cost = max(cost, _sperner_min(w), chain_distinct(ctx) - 1)
                if separation:
                    cost = max(cost, separation_clique(ctx))
            costs[Smask] = cost
        Smask = (Smask - 1) & sup
    pout = None
    if output and formula and not polarity:     # output-region costs: monotone only
        pout = {}
        for Sm, c in costs.items():
            fc = formula_dp(Sm, tuple(output_family(terms, Sm)))
            pout[Sm] = max(c, fc) if fc < _FINF else c
    return PortCosts(costs, mono=bool(mono or (formula and not polarity)), pout=pout)


_ord_cache = {}


def port_binary_lb(terms, costs, H=0):
    if ORDERED[0]:
        key = (terms, H, getattr(costs, 'fp', None) or hash(tuple(sorted(costs.items()))))
        if key not in _ord_cache:
            _ord_cache[key] = max(_port_binary_lb_unordered(terms, costs, H), ordered_port_lb(terms, costs, H))
        return _ord_cache[key]
    return _port_binary_lb_unordered(terms, costs, H)


def _port_binary_lb_unordered(terms, costs, H=0):
    """Connection bound. Cut the circuit at repeated wires: each region (terminal = a repeated wire or the
    output) has inputs S (independent in J), receives wires that cannot depend on S, and passes S on only
    through its terminal, so it needs >= p(S) incoming connections; regions without inputs need >= 1.
    Reads of repeated wires total e + r and there are r + 1 regions, so for the k regions with inputs
    sum p(S_j) <= e + k - 1, with k <= e + 1; forced-repeated inputs (H) are singleton regions.
    B = e + n - 1 for the smallest feasible e."""
    if terms == RTRUE or not terms:
        return 0
    sup = rterms_support(terms)
    n = bin(sup).count('1')
    cst = {S: c for S, c in costs.items() if not (S & H) or bin(S).count('1') == 1}
    INF = 10 ** 9
    memo = {}

    def dp(S, k):
        if S == 0:
            return 0 if k == 0 else INF
        if k <= 0 or k > bin(S).count('1'):
            return INF
        key = (S, k)
        if key in memo:
            return memo[key]
        low = S & -S
        best = INF
        part = S
        while part:
            if part & low and part in cst:
                v = cst[part] + dp(S ^ part, k - 1)
                if v < best:
                    best = v
            part = (part - 1) & S
        memo[key] = best
        return best
    for e in range(n + 2):
        for k in range(1, min(n, e + 1) + 1):
            if dp(sup, k) <= e + k - 1:
                return n - 1 + e
    return n - 1


def multi_gate_lb(masks, gates, depth, port=None):
    """Bound from several gates that each read two inputs directly (e.g. a pinned seed plus the piece gate).
    Each such gate with controlling value c makes an operand that stays essential when the other is set to c
    read again (the gate turns constant there); the forced repeats H of all gates hold together. Then:
    each gate's own pair bound; excess >= |H| (+1 if setting H to 0 leaves a non-read-once function);
    colouring and connection bounds with H as singleton regions."""
    terms = _anti(masks)
    sup = rterms_support(terms)
    m = bin(sup).count('1')
    L = rec_lb(terms, depth)
    H = set()
    for op, x, y in gates:
        if op == 2 or x >= 64 or y >= 64:
            continue
        c = int(op == 1)
        L = max(L, _pair_bound(terms, x, y, c, depth, m))
        for u, w in ((x, y), (y, x)):
            if rterms_support(rterms_restrict(terms, w, c)) >> u & 1:
                H.add(u)
    rem = terms
    for u in H:
        rem = rterms_restrict(rem, u, 0)
    L = max(L, m - 1 + len(H) + int(rterms_obstruction(rem)))
    if COLOR_BOUNDS[0]:
        rest = [v for v in range(sup.bit_length()) if sup >> v & 1 and v not in H]
        J = [p_ for p_ in incompatible_pairs(terms) if p_[0] not in H and p_[1] not in H]
        L = max(L, m - 1 + len(H) + max(0, chromatic(rest, J) - 1))
    if port is not None:
        L = max(L, port_binary_lb(terms, port, sum(1 << u for u in H)))
    return L


def ordered_port_lb(terms, costs, H=0):
    """Ordered terminal groups. Sort the groups by their terminals: an input of a later group cannot reach an
    earlier terminal (its unique path ends at its own terminal first), so group S's terminal depends only on
    S and the inputs P of earlier groups. Hence two outside assignments agreeing on P give the same
    non-constant restriction of f to S (target monotone; NOT gates allowed). Search ordered sequences of
    eligible groups with sum p(S_j) <= e + k - 1, k <= e + 1; B = e + n - 1 for the smallest feasible e."""
    if terms == RTRUE or not terms:
        return 0
    sup = rterms_support(terms)
    n = bin(sup).count('1')
    cst = {S: c for S, c in costs.items() if not (S & H) or bin(S).count('1') == 1}
    ctxs = {S: port_contexts(terms, S) for S in cst}
    elig_cache = {}

    def eligible(S, P):
        key = (S, P)
        if key in elig_cache:
            return elig_cache[key]
        seen = {}
        ok = True
        for z, sig in ctxs[S].items():
            k_ = z & P
            if k_ in seen and seen[k_] != sig:
                ok = False
                break
            seen[k_] = sig
        elig_cache[key] = ok
        return ok
    INF = 10 ** 9
    memo = {}

    def dp(P, k):            # min sum of costs to cover sup \\ P with exactly k more groups
        if P == sup:
            return 0 if k == 0 else INF
        if k <= 0:
            return INF
        key = (P, k)
        if key in memo:
            return memo[key]
        rest = sup & ~P
        best = INF
        S = rest
        while S:
            if S in cst and eligible(S, P):
                v = cst[S] + dp(P | S, k - 1)
                if v < best:
                    best = v
            S = (S - 1) & rest
        memo[key] = best
        return best
    pout = getattr(costs, 'pout', None)
    if pout:
        pout_c = {S: c for S, c in pout.items() if S in cst}
        memo2 = {}

        def dp2(P, k):        # as dp, but the last group is the output region and pays pout
            if k <= 0:
                return INF
            key = (P, k)
            if key in memo2:
                return memo2[key]
            rest = sup & ~P
            best = INF
            S = rest
            while S:
                if S in cst and eligible(S, P):
                    if P | S == sup:
                        if k == 1:
                            best = min(best, pout_c.get(S, cst[S]))
                    else:
                        v = cst[S] + dp2(P | S, k - 1)
                        if v < best:
                            best = v
                S = (S - 1) & rest
            memo2[key] = best
            return best
        # Case A: output region holds inputs (last group pays pout). Case B: the output region is empty and
        # needs >= 2 incoming wires: sum p <= e + k - 2, k <= e.
        for e in range(n + 2):
            for k in range(1, min(n, e + 1) + 1):
                if dp2(0, k) <= e + k - 1 or (k <= e and dp(0, k) <= e + k - 2):
                    return n - 1 + e
        return n - 1
    for e in range(n + 2):
        for k in range(1, min(n, e + 1) + 1):
            if dp(0, k) <= e + k - 1:
                return n - 1 + e
    return n - 1


def cube_binary_lb(masks, cube, depth, identify=False, port=None):
    """Lower bound on binary gates for circuits whose first gate is the cube's gate (reading inputs directly)."""
    terms = _anti(masks)
    whole = rec_lb(terms, depth)
    op, x, y = cube
    if op == 2:
        return max(whole, port_binary_lb(terms, port, 0)) if port is not None else whole
    sup = rterms_support(terms)
    m = bin(sup).count('1')
    L = max(whole, _pair_bound(terms, x, y, int(op == 1), depth, m))
    if port is not None:
        # first gate reads x, y directly; with controlling value c, an operand that stays essential when the
        # other is set to c must be read again: it is a forced-repeated (singleton-region) input
        c = int(op == 1)
        Hm = 0
        for u, w in ((x, y), (y, x)):
            if rterms_support(rterms_restrict(terms, w, c)) >> u & 1:
                Hm |= 1 << u
        L = max(L, port_binary_lb(terms, port, Hm))
    if identify:
        # x := y turns the first gate into a copy, x := not y into a constant: either way one binary gate
        # disappears and the rest computes the identified function.
        L = max(L, 1 + rec_lb(identify_equal(terms, x, y), depth), 1 + complementary_lb(terms, x, y, depth))
    return L


def single_not_clauses(n, masks, pool, ops):
    """Exactly one NOT gate g: every path through g is odd, so every input the target depends on needs a
    path avoiding g. Also: reading wire i at gate g while i has a path avoiding g means i is read twice."""
    cl = []
    ess = [x for x in range(n) if any(m >> x & 1 for m in masks)]
    for g in ops:
        others = [ops[h][2] for h in ops if h != g]
        for x in ess:
            cl.append([-ops[g][2], *others, pool.id(('avoid', g, x))])
        for i in range(g):
            cl.append([-pool.id(('uses', g, i)), -pool.id(('avoid', g, i)), pool.id(('repeat', i))])
    return cl


def polaritydom_clauses(n, masks, rows, pool, ops):
    """If flipping x at row z changes f and gate g lies on every path from x (no 'avoid' path), the change
    reaches the output only through g: if g's value matches f(z) there is an even-NOT path from g, if it is
    opposite there is an odd one. Needs --parity (one-directional even/odd path witnesses) and --bypass."""
    T = lambda y: any(y & m == m for m in masks)
    cl = []
    for z in rows:
        for x in range(n):
            if T(z) == T(z ^ (1 << x)):
                continue
            for g in list(ops)[:-1]:
                av = pool.id(('avoid', g, x))
                v = pool.id(('val', z, g))
                match = v if T(z) else -v
                cl += [[av, -match, pool.id(('even', g))], [av, match, pool.id(('odd', g))]]
    return cl


def add_color_rules(n, G, masks, pool, ops, clauses, pairro=False, budget=False, sharecolor=False,
                    activecolor=False, colorzero=False, isolatedcolor=False):
    """Needs --readonce (multi, repeat, uses variables).
    pairro: an incompatible pair cannot both occur once in the unfolded formula: M[x] or M[y].
    budget: inputs with the same first shared wire (a repeated wire or the output) are compatible, and
      repeated inputs outside S cannot be terminals for S, so sum_{v in S} R[v] + sum_internal R[j]
      >= chi(J[S]) - 1 (S = all inputs and each maximal clique of J).
    sharecolor: colour wires with G - n + 2 colours; a non-repeated wire takes its unique reader's colour;
      incompatible inputs get different colours (terminals <= excess + 1 <= G - n + 2)."""
    out = n + G - 1
    terms = _anti(masks)
    J = incompatible_pairs(terms)
    ess = [v for v in range(n) if any(m >> v & 1 for m in masks)]
    if pairro:
        for x, y in J:
            clauses.append([pool.id(('multi', x)), pool.id(('multi', y))])
    if budget:
        internal = [pool.id(('repeat', j)) for j in ops if j != out]
        subsets = [tuple(ess)]
        adj = {v: set() for v in ess}
        for a, b in J:
            adj[a].add(b); adj[b].add(a)
        def bk(R_, P, X):                       # Bron-Kerbosch maximal cliques
            if not P and not X:
                if len(R_) >= 3:
                    subsets.append(tuple(sorted(R_)))
                return
            for v in list(P):
                bk(R_ | {v}, P & adj[v], X & adj[v]); P = P - {v}; X = X | {v}
        bk(set(), set(ess), set())
        for S in subsets:
            need = chromatic(S, [p_ for p_ in J if p_[0] in S and p_[1] in S]) - 1
            lits = [pool.id(('repeat', v)) for v in S] + internal
            if need > len(lits):
                clauses.append([])
            elif need > 0:
                clauses.extend(CardEnc.atleast(lits, bound=need, vpool=pool).clauses)
    if sharecolor:
        K = G - n + 2
        if K < 1:
            clauses.append([]); return
        col = {(i, c): pool.id(('color', i, c)) for i in range(out + 1) for c in range(K)}
        for i in range(out + 1):
            clauses.extend(CardEnc.equals([col[i, c] for c in range(K)], 1, vpool=pool).clauses)
        clauses.append([col[out, 0]])
        for i in range(out):
            ri = pool.id(('repeat', i))
            for j in range(max(n, i + 1), out + 1):
                u = pool.id(('uses', j, i))
                for c in range(K):
                    clauses.append([-u, ri, -col[i, c], col[j, c]])
        for x, y in J:
            for c in range(K):
                clauses.append([-col[x, c], -col[y, c]])
        # All three below hold for the canonical colouring (one colour per repeated wire and the output).
        if activecolor:
            active = [pool.id(('activecol', c)) for c in range(K)]
            for i in range(out + 1):
                for c in range(K):
                    clauses.append([-col[i, c], active[c]])
            clauses.extend(CardEnc.atmost(active + [ops[j][2] for j in ops], bound=K, vpool=pool).clauses)
            reps = [pool.id(('repeat', i)) for i in range(out)]
            clauses.extend(CardEnc.atmost(active + [-r for r in reps], bound=len(reps) + 1, vpool=pool).clauses)
        if colorzero:                      # terminal is the output iff exactly one path to the output
            for i in range(out + 1):
                mi = pool.id(('multi', i))
                clauses.extend([[mi, col[i, 0]], [-mi, -col[i, 0]]])
        if isolatedcolor:                  # a repeated input is its own terminal; no other input ends there
            for x in range(n):
                rx = pool.id(('repeat', x))
                for y in range(n):
                    if y != x:
                        for c in range(K):
                            clauses.append([-rx, -col[x, c], -col[y, c]])


def rowtyped_clauses(n, masks, rows, pool, ops):
    """Monotone circuits only. On a false row z let D(z) be the inputs whose flip makes f true. Fixing all
    other inputs to z leaves exactly OR(D(z)); every gate that is 1 at z becomes constant 1, so at least
    |D(z)| - 1 OR gates are 0 at z."""
    target = lambda y: any(y & m == m for m in masks)
    cl = []
    for z in rows:
        if target(z):
            continue
        need = sum(1 for x in range(n) if not z >> x & 1 and target(z | 1 << x)) - 1
        if need <= 0:
            continue
        wit = []
        for j, (a, o, no) in ops.items():
            t = pool.id(('rowtyped', z, j)); wit.append(t)
            cl += [[-t, o], [-t, -pool.id(('val', z, j))]]
        if need > len(wit):
            cl.append([])
        else:
            cl.extend(CardEnc.atleast(wit, bound=need, vpool=pool).clauses)
    return cl


def sens_clauses(n, masks, pool, ops, select):
    """For each edge {x, z}: rows e_z (f = 0) and e_x + e_z (f = 1) differ only in x, so some gate that
    reads x must take different values on them (otherwise every wire, the output included, agrees).
    Both rows are always among the initial rows."""
    cl = []
    for m in masks:
        u, v = [i for i in range(n) if m >> i & 1]
        for x, z in ((u, v), (v, u)):
            a, b = 1 << z, m
            ts = []
            for j in ops:
                va, vb = pool.id(('val', a, j)), pool.id(('val', b, j))
                t = pool.id(('sens', a, b, j))
                cl += [[-t, select[j, 0][x], select[j, 1][x]], [-t, va, vb], [-t, -va, -vb]]
                ts.append(t)
            cl.append(ts)
    return cl


def add_minimality_rules(n, G, ops, select, clauses):
    """Valid ONLY when every smaller size is already ruled out (exact G-1 and G-2 UNSAT), so any circuit
    found is a minimum one. A minimum circuit has (a) no two gates with the same operation and operands,
    (b) no absorption/idempotence AND|OR(i, k) with k = AND|OR(i, .) (equals k or i), (c) no
    AND|OR(i, NOT i) (a constant). (a) uses that equal (right, left) keys are adjacent under the colex
    order and can be swapped, so ordering their operations is a refinement of the canonical choice."""
    output = n + G - 1
    for j in ops:
        if j == output:
            continue
        l0, r0, l1, r1 = select[j, 0], select[j, 1], select[j + 1, 0], select[j + 1, 1]
        for r in range(j):
            for l in range(r + 1):
                for p in range(3):
                    for q in range(p + 1):
                        clauses.append([-r0[r], -r1[r], -l0[l], -l1[l], -ops[j][p], -ops[j + 1][q]])
    for j in ops:
        for k in range(n, j):
            for i in range(k):
                for kk in range(2):
                    clauses.append([-select[j, 0][i], -select[j, 1][k], ops[j][2], ops[k][2], -select[k, kk][i]])
                clauses.append([-select[j, 0][i], -select[j, 1][k], ops[j][2], -ops[k][2], -select[k, 0][i]])


_SCACHE = {}     # persistent solvers for flags['reuse'] (one per worker process)


class _Keep:
    """Context wrapper that does not close a cached solver."""

    def __init__(self, s):
        self.s = s

    def __enter__(self):
        return self.s

    def __exit__(self, *a):
        return False


class RebuildSolver:
    """Wrapper for non-incremental solvers such as Kissat: keeps every clause and builds a fresh solver per
    solve call (assumptions passed as unit clauses). Interrupts are ignored; cap such runs by killing them."""

    def __init__(self, name, bootstrap_with=()):
        self.name, self.cl, self.model, self.stats, self.last = name, [list(c) for c in bootstrap_with], None, {}, None

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False

    def append_formula(self, f):
        self.cl.extend(list(c) for c in f)

    def add_clause(self, c):
        self.cl.append(list(c))

    def interrupt(self):
        pass

    def solve_limited(self, assumptions=(), expect_interrupt=False):
        return self.solve(assumptions)

    def solve(self, assumptions=()):
        with Solver(name=self.name, bootstrap_with=self.cl + [[a] for a in assumptions]) as t:
            r = t.solve()
            self.model = t.get_model() if r else None
            st = t.accum_stats() or {}
            for k, v in st.items():
                self.stats[k] = self.stats.get(k, 0) + v
            self.nv = t.nof_vars()
        return r

    def get_model(self):
        return self.model

    def accum_stats(self):
        return self.stats

    def nof_vars(self):
        return getattr(self, 'nv', 0)

    def nof_clauses(self):
        return len(self.cl)


def evaluate(n, circ, x):
    v = [bool(x >> i & 1) for i in range(n)]
    for op, l, r in circ:
        v.append(v[l] and v[r] if op == 0 else v[l] or v[r] if op == 1 else not v[l])
    return v[-1]


def run_cube(args):
    n, masks, G, solver_name, cube, fanout, readonce = args[:7]
    flags = args[7] if len(args) > 7 else {}
    if os.path.exists(STOP):
        return cube, 'STOPPED', None, 0.0, ''
    target = lambda x: any(x & m == m for m in masks)
    N = 1 << n
    t0 = time.time()
    REC_CLOSURE[0] = bool(flags.get('recclosure'))
    COLOR_BOUNDS[0] = bool(flags.get('colorbounds'))
    MONO[0] = bool(flags.get('nonot'))
    ORDERED[0] = bool(flags.get('orderedports'))
    if (flags.get('monoports') or getattr(flags.get('portcosts'), 'mono', False)) and not flags.get('nonot'):
        raise ValueError('monotone port bounds require a monotone (NOT-free) search')
    reuse = bool(flags.get('reuse')) and bool(flags.get('fixgates')) and not solver_name.startswith('kissat')
    piece = flags['fixgates'][-1] if reuse else None
    rkey = repr((n, tuple(masks), G, solver_name, cube, fanout, readonce,
                 sorted((k, repr(v)) for k, v in flags.items() if k not in ('fixgates', 'portcosts')),
                 tuple(flags['fixgates'][:-1]))) if reuse else None
    cached = _SCACHE.get(rkey) if reuse else None
    if flags.get('recursivebounds'):
        Lc = cube_binary_lb(masks, cube, flags.get('recdepth', 2), identify=flags.get('identifybounds', False),
                            port=flags.get('portcosts'))
        Lc_base = Lc
        pinned = [cube] + [(fop, fl, fr) for off, fop, fl, fr in flags.get('fixgates', ()) if fl < n and fr < n]
        if len(pinned) > 1:
            Lc = max(Lc, multi_gate_lb(masks, pinned, flags.get('recdepth', 2), port=flags.get('portcosts')))
        if Lc > G:
            return cube, 'UNSAT', None, time.time() - t0, f'analytical: binary-gate bound {Lc} > {G}'
        if Lc > G:
            return cube, 'UNSAT', None, time.time() - t0, f'analytical: binary-gate bound {Lc} > {G}'
    if cached:
        output, pool, ops, select = cached['output'], cached['pool'], cached['ops'], cached['select']
        clauses = None
    else:
        output, pool, clauses, ops, select = build(n, G, flags.get('colex_from', 0))
        if flags.get('nonot'):                  # monotone search: no NOT gates
            clauses.extend([[-ops[j][2]] for j in ops])
            if flags.get('typed'):
                # Zero certificates pick one false input per AND gate: #maximal independent sets <= 2^#AND;
                # dually #edges (minimal true sets) <= 2^#OR.
                tgt = lambda y: any(y & mm == mm for mm in masks)
                nmis = sum(1 for y in range(1 << n) if not tgt(y)
                           and all(tgt(y | 1 << i) for i in range(n) if not y >> i & 1))
                for lits, need in (([ops[j][0] for j in ops], (nmis - 1).bit_length()),
                                   ([ops[j][1] for j in ops], (len(masks) - 1).bit_length())):
                    if need > len(lits):
                        clauses.append([])
                    elif need > 0:
                        clauses.extend(CardEnc.atleast(lits, bound=need, vpool=pool).clauses)
        for off, fop, fl, fr in (flags.get('fixgates', ())[:-1] if reuse else flags.get('fixgates', ())):   # extra gates pinned by the caller (e.g. a shard seed)
            j = n + off
            clauses.extend([[select[j, 0][fl]], [select[j, 1][fr]], [ops[j][fop]]])
        if flags.get('recursivebounds') and G - (Lc_base if reuse else Lc) < G:
            clauses.extend(CardEnc.atmost([ops[j][2] for j in ops], bound=max(0, G - (Lc_base if reuse else Lc)), vpool=pool).clauses)
        if fanout:
            add_fanout_rules(n, masks, ops, select, clauses)
        if readonce:
            add_readonce_rules(n, G, masks, pool, ops, select, clauses, parity=flags.get('parity', False))
        if flags.get('minimal'):
            add_minimality_rules(n, G, ops, select, clauses)
        if flags.get('closedcone') and readonce:
            add_closedcone_rules(n, G, masks, pool, ops, select, clauses)
        if flags.get('outdec'):
            add_outdec_rules(n, G, masks, pool, ops, select, clauses)
        if flags.get('bottleneck') and readonce:
            add_bottleneck_rules(n, G, masks, pool, ops, select, clauses)
        if flags.get('elim'):
            add_elim_rules(n, G, masks, pool, ops, select, clauses, strong=flags.get('strongbounds', False),
                           closure=flags.get('elimclosure', False),
                           recdepth=flags.get('recdepth', 2) if flags.get('recursivebounds') else 0,
                           fanoutelim=flags.get('fanoutelim', False) and readonce,
                           lostreader=flags.get('lostreader', False))
        if flags.get('strongbounds'):
            add_global_not_bound(n, G, masks, pool, ops, clauses)
        if readonce and (flags.get('pairro') or flags.get('colorbudget') or flags.get('sharecolor')):
            add_color_rules(n, G, masks, pool, ops, clauses, pairro=flags.get('pairro', False),
                            budget=flags.get('colorbudget', False), sharecolor=flags.get('sharecolor', False),
                            activecolor=flags.get('activecolor', False), colorzero=flags.get('colorzero', False),
                            isolatedcolor=flags.get('isolatedcolor', False))
        if flags.get('readerbudget') and readonce:
            add_readerbudget(n, G, masks, pool, ops, clauses)

    cert = bool(flags.get('cert')) and bool(flags.get('nonot'))

    def row(x):
        val = [pool.id(('val', x, j)) for j in range(output + 1)]
        yield from ([val[i] if x >> i & 1 else -val[i]] for i in range(n))
        if cert:
            # Monotone certificates: on a true row, val = 1 must be justified (val -> gate true); on a false
            # row, val = 0 must be justified (not val -> gate false). Actual values satisfy these, so every
            # other rule stays sound; a certified output is correct on that row (models are re-verified).
            t = target(x)
            for j, (a, o, no) in ops.items():
                l, r = [pool.id(('arg', x, j, k)) for k in range(2)]
                for k, arg in enumerate((l, r)):
                    for i, sel in enumerate(select[j, k]):
                        yield [-sel, -arg, val[i]] if t else [-sel, arg, -val[i]]
                f = val[j]
                if t:
                    yield from ([-a, l, -f], [-a, r, -f], [-o, l, r, -f])
                else:
                    yield from ([-a, -l, -r, f], [-o, -l, f], [-o, -r, f])
            yield [val[-1] if t else -val[-1]]
            return
        for j, (a, o, no) in ops.items():
            l, r = [pool.id(('arg', x, j, k)) for k in range(2)]
            for k, arg in enumerate((l, r)):
                for i, sel in enumerate(select[j, k]):
                    yield [-sel, -arg, val[i]]
                    yield [-sel, arg, -val[i]]
            f = val[j]
            yield from ([-a, -l, -r, f], [-a, l, -f], [-a, r, -f], [-o, l, r, -f], [-o, -l, f],
                        [-o, -r, f], [-no, -l, -f], [-no, l, f])
        yield [val[-1] if target(x) else -val[-1]]

    op, lo, hi = cube
    assume = [ops[n][op], select[n, 0][lo], select[n, 1][hi]]
    piece_assume = []
    if reuse:
        poff, pop_, pl, pr = piece
        pj = n + poff
        piece_assume = [select[pj, 0][pl], select[pj, 1][pr], ops[pj][pop_]]
    if cached:
        ctx = _Keep(cached['s'])
    elif reuse:
        ctx = _Keep(Solver(name=solver_name, bootstrap_with=clauses))
    else:
        ctx = (RebuildSolver(solver_name, clauses) if solver_name.startswith('kissat')
               else Solver(name=solver_name, bootstrap_with=clauses))
    with ctx as s:
        done = threading.Event()

        def watch():
            while not done.wait(5):
                if os.path.exists(STOP):
                    s.interrupt()
                    return
        threading.Thread(target=watch, daemon=True).start()
        if cached:
            rows = cached['rows']
            if flags.get('units'):
                assume = []
        else:
            rows = {0, N - 1, *masks, *(1 << i for i in range(n))}
            rows |= {x for x in range(N) if not target(x)
                     and all(target(x | 1 << i) for i in range(n) if not x >> i & 1)}
            for x in rows:
                s.append_formula(list(row(x)))
            if flags.get('sens'):
                s.append_formula(sens_clauses(n, masks, pool, ops, select))
            if flags.get('bypass') and readonce:
                byp = []
                add_bypass_rules(n, G, masks, rows, pool, ops, select, byp)
                s.append_formula(byp)
            if flags.get('signeddom') and flags.get('bypass') and readonce:
                s.append_formula(signeddom_clauses(n, masks, rows, pool, ops))
            if flags.get('elimbypass') and flags.get('elim') and flags.get('bypass') and readonce:
                s.append_formula(elimbypass_clauses(n, masks, pool, ops, closure=flags.get('elimclosure', False)))
            if flags.get('notbypass') and flags.get('bypass') and readonce:
                s.append_formula(single_not_clauses(n, masks, pool, ops))
            if flags.get('polaritydom') and flags.get('bypass') and flags.get('parity') and readonce:
                s.append_formula(polaritydom_clauses(n, masks, rows, pool, ops))
            if flags.get('elimlink') and flags.get('elim') and not flags.get('elimclosure'):
                s.append_formula(elimlink_clauses(n, masks, rows, pool, ops))
            if flags.get('readersens'):
                s.append_formula(readersens_clauses(n, masks, rows, pool, ops, select))
            if flags.get('usens') and readonce:
                s.append_formula(usens_clauses(n, masks, rows, pool, ops, select))
            if flags.get('rowtyped') and flags.get('nonot'):
                s.append_formula(rowtyped_clauses(n, masks, rows, pool, ops))
            if flags.get('units'):          # fix the cube as unit clauses: top-level simplification
                for lit in assume:
                    s.add_clause([lit])
                assume = []
            if reuse:
                _SCACHE[rkey] = dict(s=s, rows=rows, output=output, pool=pool, ops=ops, select=select)
        assume = assume + piece_assume
        status = 'UNSAT'
        circ = None
        sat_time = 0.0; iters = 0
        while True:
            ts = time.perf_counter()
            res = s.solve_limited(assumptions=assume, expect_interrupt=True)
            sat_time += time.perf_counter() - ts; iters += 1
            if res is None:
                status = 'STOPPED'
                break
            if not res:
                break
            m = set(s.get_model())
            c = [(next(k for k, v in enumerate(ops[j]) if v in m),
                  *(next(i for i, v in enumerate(select[j, k]) if v in m) for k in range(2))) for j in ops]
            bad = [x for x in range(N) if evaluate(n, c, x) != target(x)]
            if not bad:
                status, circ = 'WITNESS', c
                break
            for x in bad:
                s.append_formula(list(row(x)))
            rows.update(bad)
        done.set()
        st = s.accum_stats() or {}
        stats = (f"solve={sat_time:.1f}s iters={iters} vars={s.nof_vars()} clauses={s.nof_clauses()} "
                 f"rows={len(rows)} conflicts={st.get('conflicts', '?')} "
                 f"decisions={st.get('decisions', '?')} propagations={st.get('propagations', '?')}")
        return cube, status, circ, time.time() - t0, stats


def automorphisms(n, edges):
    E = {frozenset(e) for e in edges}
    deg = [sum(v in e for e in E) for v in range(n)]
    out = []

    def bt(mp):
        k = len(mp)
        if k == n:
            out.append(tuple(mp)); return
        for c in range(n):
            if c not in mp and deg[c] == deg[k] and all(
                    (frozenset((mp[i], c)) in E) == (frozenset((i, k)) in E) for i in range(k)):
                bt(mp + [c])
    bt([])
    return out


def orbit_min(cube, auts):
    """True if the cube's input pair is the least (in the gate order's (right, left) key) in its orbit.
    If a circuit exists, some relabelled copy of it, put in canonical gate order, starts with such a
    pair: the first gate of a canonical circuit is its least input-only gate."""
    op, l, r = cube
    key = (r, l)
    for p in auts:
        a, b = sorted((p[l], p[r]))
        if (b, a) < key:
            return False
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--edges', required=True)
    ap.add_argument('--size', type=int, required=True)
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--solver', default='maplechrono')
    ap.add_argument('--log', default=None)
    ap.add_argument('--skip-log', action='append', default=[], help='skip pieces already UNSAT in this log')
    ap.add_argument('--symmetry', action='store_true', help='search only orbit-least pieces under graph automorphisms')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--fanout', action='store_true', help='add the graph-specific fan-out rules')
    ap.add_argument('--readonce', action='store_true', help='add repeated-wire budget and read-once obstructions')
    ap.add_argument('--sens', action='store_true', help='add edge sensitivity clauses')
    ap.add_argument('--parity', action='store_true', help='with --readonce: every input needs an even-NOT path')
    ap.add_argument('--usens', action='store_true', help='with --readonce: unique-reader sensitivity')
    ap.add_argument('--closedcone', action='store_true',
                    help='with --readonce: closed-cone obstruction (only acts on connected, twin-free, non-read-once graphs)')
    ap.add_argument('--bypass', action='store_true', help='with --readonce: controlling-value bypass + dominator sensitivity')
    ap.add_argument('--outdec', action='store_true', help='output-gate decomposition rules')
    ap.add_argument('--bottleneck', action='store_true', help='with --readonce: information bottlenecks for 2- and 3-input sets')
    ap.add_argument('--elim', action='store_true', help='restriction gate-elimination bounds')
    ap.add_argument('--strongbounds', action='store_true',
                    help='analytical m+1 / m+2 binary-gate bounds (global NOT bound; strengthens --elim)')
    ap.add_argument('--units', action='store_true', help='fix the cube with unit clauses, not assumptions')
    ap.add_argument('--minimal', action='store_true',
                    help='minimality rules: ONLY sound if sizes size-1 and size-2 are already UNSAT')
    ap.add_argument('--trust-log', action='append', default=[],
                    help='like --skip-log, for an older log without an edge list that you vouch is this exact graph')
    ap.add_argument('--elimbypass', action='store_true', help='with --elim --bypass: constant gates force bypass paths')
    ap.add_argument('--elimlink', action='store_true', help='with --elim: constant flags fix row values')
    ap.add_argument('--readersens', action='store_true', help='some reader of a sensitive input is non-controlled')
    ap.add_argument('--readerbudget', action='store_true', help='with --readonce: binary readers of x + #NOT <= G - L_x')
    ap.add_argument('--elimclosure', action='store_true', help='with --elim: also fix inputs made inessential')
    ap.add_argument('--signeddom', action='store_true', help='with --bypass: signed dominator sensitivity')
    ap.add_argument('--recursivebounds', action='store_true',
                    help='recursive analytical binary-gate bounds per cube (may reject cubes before SAT)')
    ap.add_argument('--recdepth', type=int, default=2)
    ap.add_argument('--notbypass', action='store_true', help='with --bypass: exactly-one-NOT rules')
    ap.add_argument('--recclosure', action='store_true', help='with --recursivebounds: restriction-closure bounds')
    ap.add_argument('--identifybounds', action='store_true', help='with --recursivebounds: x=y / x=-y bounds')
    ap.add_argument('--fanoutelim', action='store_true', help='with --elim --elimclosure --readonce: lost sharing')
    ap.add_argument('--pairro', action='store_true', help='with --readonce: incompatible pairs need a multi-path input')
    ap.add_argument('--colorbounds', action='store_true', help='with --recursivebounds: chromatic-number bounds')
    ap.add_argument('--colorbudget', action='store_true', help='with --readonce: repeated wires >= chi(J[S]) - 1')
    ap.add_argument('--sharecolor', action='store_true', help='with --readonce: first-shared-wire colouring')
    ap.add_argument('--lostreader', action='store_true', help='with --fanoutelim: constant readers lose sharing')
    ap.add_argument('--activecolor', action='store_true', help='with --sharecolor: colours used <= repeats + 1, + #NOT budget')
    ap.add_argument('--colorzero', action='store_true', help='with --sharecolor: colour 0 iff single path to output')
    ap.add_argument('--isolatedcolor', action='store_true', help='with --sharecolor: repeated inputs get unique colours')
    ap.add_argument('--portbounds', action='store_true', help='with --recursivebounds: region connection bound')
    ap.add_argument('--monoports', action='store_true', help='with --portbounds, monotone circuits only: Sperner/chain ports')
    ap.add_argument('--orderedports', action='store_true', help='with --portbounds: ordered terminal groups')
    ap.add_argument('--formulaports', action='store_true',
                    help='with --portbounds: regional formula costs (polarity version, valid with NOT gates)')
    ap.add_argument('--polaritydom', action='store_true', help='with --bypass --parity: polarity dominator')
    ap.add_argument('--fast', action='store_true',
                    help='recommended set (benchmarked 2026-11-23): --symmetry --fanout --readonce --sens --units '
                         '--usens --bypass --elim --elimclosure --signeddom --recursivebounds --notbypass '
                         '--recclosure --identifybounds --fanoutelim --pairro --colorbounds --sharecolor --colorbudget')
    a = ap.parse_args()
    if a.fast:
        for k in ('symmetry', 'fanout', 'readonce', 'sens', 'units', 'usens', 'bypass', 'elim',
                  'elimclosure', 'signeddom', 'recursivebounds', 'notbypass', 'recclosure',
                  'identifybounds', 'fanoutelim', 'pairro', 'colorbounds', 'sharecolor', 'colorbudget'):
            setattr(a, k, True)
    log = open(a.log, 'a', encoding='utf-8') if a.log else None

    def say(msg):
        line = f'{time.strftime("%H:%M:%S")} {msg}'
        print(line, flush=True)
        if log:
            log.write(line + '\n'); log.flush()

    if os.path.exists(STOP):
        os.remove(STOP)
    n = a.n
    edges = [tuple(map(int, e.split('-'))) for e in a.edges.split(',')]
    masks = [(1 << u) | (1 << v) for u, v in edges]
    allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)] + [(2, i, i) for i in range(n)]
    import re
    done_before = set()
    edge_key = ','.join(f'{min(e)}-{max(e)}' for e in sorted(tuple(sorted(e)) for e in edges))
    for path, trusted in [(x, False) for x in a.skip_log] + [(x, True) for x in a.trust_log]:
        ok = False      # only trust UNSAT lines under a header for this exact problem
        for line in open(path, encoding='utf-8'):
            h = re.search(r'(?:search|resume|tail-filler): n=(\d+), (\d+) edges, exactly (\d+) gates', line)
            if h:
                ek = re.search(r'edges=(\S+)', line)
                ok = (int(h.group(1)), int(h.group(2)), int(h.group(3))) == (n, len(edges), a.size) and                     ((ek is not None and ek.group(1).rstrip('.;,') == edge_key) or (ek is None and trusted))
                continue
            mm = re.search(r'cube \((\d+), (\d+), (\d+)\): UNSAT', line)
            if mm and ok:
                done_before.add(tuple(map(int, mm.groups())))
    auts = automorphisms(n, edges) if a.symmetry else [tuple(range(n))]
    sym = [c for c in allc if orbit_min(c, auts)]
    cubes = sorted((c for c in sym if c not in done_before), key=lambda c: (c[2], c[1], c[0]))
    say(f'search: n={n}, {len(edges)} edges, exactly {a.size} gates (at most {max(0, a.size - n + 1)} NOT); '
        f'{len(allc)} pieces, {len(allc) - len(sym)} skipped by symmetry ({len(auts)} automorphisms), '
        f'{len(sym) - len(cubes)} already UNSAT in logs, {len(cubes)} to run; {a.workers} workers, {a.solver}'
        f'{", fan-out rules" if a.fanout else ""}{", read-once rules" if a.readonce else ""}'
        f'{", sensitivity" if a.sens else ""}{", unit cubes" if a.units else ""}'
        f'{", parity" if a.parity else ""}{", unique-reader sensitivity" if a.usens else ""}'
        f'{", closed-cone" if a.closedcone else ""}{", bypass" if a.bypass else ""}'
        f'{", output decomposition" if a.outdec else ""}{", bottlenecks" if a.bottleneck else ""}'
        f'{", elimination" if a.elim else ""}{", strong bounds" if a.strongbounds else ""}'
        f'{", elim-bypass" if a.elimbypass else ""}{", elim-link" if a.elimlink else ""}'
        f'{", reader-sens" if a.readersens else ""}{", reader-budget" if a.readerbudget else ""}'
        f'{", elim-closure" if a.elimclosure else ""}{", signed-dominator" if a.signeddom else ""}'
        f'{", recursive bounds (depth " + str(a.recdepth) + ")" if a.recursivebounds else ""}'
        f'{", not-bypass" if a.notbypass else ""}{", polarity-dominator" if a.polaritydom else ""}'
        f'{", rec-closure" if a.recclosure else ""}{", identify-bounds" if a.identifybounds else ""}'
        f'{", fanout-elim" if a.fanoutelim else ""}{", pair-ro" if a.pairro else ""}'
        f'{", color-bounds" if a.colorbounds else ""}{", color-budget" if a.colorbudget else ""}'
        f'{", share-color" if a.sharecolor else ""}{", lost-reader" if a.lostreader else ""}'
        f'{", active-color" if a.activecolor else ""}{", color-zero" if a.colorzero else ""}'
        f'{", isolated-color" if a.isolatedcolor else ""}{", port-bounds" if a.portbounds else ""}'
        f'{", MINIMALITY RULES (requires sizes " + str(a.size - 1) + " and " + str(a.size - 2) + " UNSAT)" if a.minimal else ""}'
        f'; edges={edge_key}. '
        f'Stop with: create file {STOP}')
    say('pieces to run: ' + ' '.join(f'{"AND OR NOT".split()[c[0]]}{c[1:] if c[0] < 2 else (c[1],)}' for c in cubes))
    if a.dry_run or not cubes:
        say('RESULT: ' + ('dry run' if cubes else 'ALL UNSAT (nothing left)')); return
    t0 = time.time()
    done = 0; times = []; result = 'ALL UNSAT'
    with Pool(a.workers) as p:
        for cube, status, circ, dt, stats in p.imap_unordered(
                run_cube, [(n, masks, a.size, a.solver, c, a.fanout, a.readonce,
                            dict(sens=a.sens, units=a.units, minimal=a.minimal, parity=a.parity, usens=a.usens,
                                 closedcone=a.closedcone, bypass=a.bypass, outdec=a.outdec,
                                 bottleneck=a.bottleneck, elim=a.elim, strongbounds=a.strongbounds,
                                 elimbypass=a.elimbypass, elimlink=a.elimlink, readersens=a.readersens,
                                 readerbudget=a.readerbudget, elimclosure=a.elimclosure,
                                 signeddom=a.signeddom, recursivebounds=a.recursivebounds,
                                 recdepth=a.recdepth, notbypass=a.notbypass,
                                 polaritydom=a.polaritydom, recclosure=a.recclosure,
                                 identifybounds=a.identifybounds, fanoutelim=a.fanoutelim, pairro=a.pairro,
                                 colorbounds=a.colorbounds, colorbudget=a.colorbudget, sharecolor=a.sharecolor,
                                 lostreader=a.lostreader, activecolor=a.activecolor, colorzero=a.colorzero,
                                 isolatedcolor=a.isolatedcolor,
                                 orderedports=a.orderedports,
                                 portcosts=port_costs(_anti(masks), mono=a.monoports, formula=a.formulaports,
                                                     polarity=not a.monoports) if a.portbounds else None))
                for c in cubes]):
            done += 1; times.append(dt)
            say(f'[{done}/{len(cubes)}] cube {cube}: {status} in {dt:.0f}s '
                f'(elapsed {time.time() - t0:.0f}s, median cube {sorted(times)[len(times) // 2]:.0f}s) {stats}')
            if status == 'WITNESS':
                ok = all(evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
                say(f'WITNESS verified={ok}: {circ}')
                result = 'WITNESS' if ok else 'MODEL FAILED VERIFICATION (encoding bug)'
                p.terminate()
                break
            if status == 'STOPPED':
                result = 'STOPPED'
    say(f'RESULT: {result} (exactly {a.size} gates) after {time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
