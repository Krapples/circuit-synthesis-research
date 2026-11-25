"""SSV exact synthesis for the free-NOT AND/OR basis (= AIG node count), complete or partial single-output functions.

Encoding (single selection variable per fanin pair, as in Kojevnikov-Kulikov-Yaroslavtsev / Haaswijk-Soeken / Percy):
  steps i = n..n+k-1, fanins j < l < i selected by s[i][(j, l)] (exactly one), operator one-hot o[i][q] over the four
  *normal* AND-type operators (f(0,0) = 0): a&b, a&~b, ~a&b, a|b. Every AND-type gate with free complementation is a
  normal gate with an inverted output, and output inversions are pushed to consumers (which can complement one or both
  operands through these four types) and finally to the circuit output, so normal chains with a free output inverter
  are complete for AIG size. Row 0 (all inputs 0) evaluates to 0 at every normal node; the target is complemented
  when it is 1 at row 0, and when row 0 is a don't-care a free output-inverter variable is used instead.
Symmetry breaking (all sound for minimum size, each optional):
  alonce    every step except the last is a fanin of a later step (exact-k "all steps used")
  colex     consecutive steps have co-lexicographically non-decreasing fanin pairs (l, j)
  oplex     consecutive steps with the same fanins have strictly increasing operators
  noreapply step i+1 does not read step i together with one of step i's own fanins under the same operator family
            (only the AND-AND / OR-OR absorbing cases, which are always redundant)
CEGAR: rows are added lazily; a SAT model is simulated on all care rows and the first violated row is added.
Optimality: exact-k with alonce UNSAT for every k in [start, K) and SAT at K proves minimum K provided every circuit
with fewer than `start` gates is excluded (start = a proved lower bound): a smaller circuit minus its unused gates would
be an all-used circuit of some size in [start, K).

API: exists(n, tt, care, k, ...) -> (status, gates, out); minimum(n, tt, care, start, ...) -> dict.
Gate format (shared with sat-search/baselines): gates = [[f4, a, b], ...], node ids 0..n-1 inputs, n+j gate j,
f4 bit (va | vb << 1) is the gate output; out = [node, inv]."""
import sys, os, time
from itertools import combinations
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(os.path.join(os.path.dirname(HERE), '.scratch-sat'))
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

# normal AND-type operators as f(a, b) on (a, b) in {(1,0), (0,1), (1,1)}; index p = a | b << 1
OPS = ((0, 0, 1),   # a & b
       (1, 0, 0),   # a & ~b
       (0, 1, 0),   # ~a & b
       (1, 1, 1))   # a | b
AND_LIKE = (0,)     # absorbing family for noreapply: AND (a&b) ...
OR_LIKE = (3,)      # ... and OR (a|b)


def op_value(q, a, b):
    return 0 if not (a or b) else OPS[q][(a | b << 1) - 1]


class Encoding:
    def __init__(self, n, k, target, care, solver='cadical195', sym=('alonce', 'colex', 'oplex', 'noreapply')):
        self.n, self.k, self.care = n, k, care
        self.free_inv = not (care & 1)
        self.target = target ^ ((1 << (1 << n)) - 1 if (care & 1) and (target & 1) else 0)
        self.inv_fixed = 1 if (care & 1) and (target & 1) else 0
        self.pool = IDPool(); v = self.pool.id
        self.steps = range(n, n + k)
        self.pairs = {i: [(j, l) for l in range(i) for j in range(l)] for i in self.steps}
        self.s = {(i, p): v(('s', i, p)) for i in self.steps for p in self.pairs[i]}
        self.o = {(i, q): v(('o', i, q)) for i in self.steps for q in range(4)}
        self.inv = v('inv') if self.free_inv else None
        self.solver = Solver(name=solver)
        add = self.solver.add_clause
        for i in self.steps:
            for enc in (CardEnc.equals([self.s[i, p] for p in self.pairs[i]], 1, vpool=self.pool, encoding=EncType.seqcounter),
                        CardEnc.equals([self.o[i, q] for q in range(4)], 1, vpool=self.pool, encoding=EncType.pairwise)):
                for c in enc.clauses:
                    add(c)
        last = n + k - 1
        if 'alonce' in sym:
            for i in self.steps:
                if i < last:
                    add([self.s[i2, p] for i2 in self.steps if i2 > i for p in self.pairs[i2] if i in p])
        key = lambda p: (p[1], p[0])
        for i in self.steps:
            if i + 1 > last:
                continue
            for p in self.pairs[i]:
                for p2 in self.pairs[i + 1]:
                    if 'colex' in sym and key(p2) < key(p):
                        add([-self.s[i, p], -self.s[i + 1, p2]])
                    elif 'oplex' in sym and p2 == p:
                        for q in range(4):
                            for q2 in range(q + 1):
                                add([-self.s[i, p], -self.s[i + 1, p], -self.o[i, q], -self.o[i + 1, q2]])
            if 'noreapply' in sym:
                # g = x op y and h = g op x (op both AND or both OR) gives h = g: redundant
                for p in self.pairs[i]:
                    for x in p:
                        p2 = (min(x, i), max(x, i))
                        for fam in (AND_LIKE, OR_LIKE):
                            for q in fam:
                                add([-self.s[i, p], -self.s[i + 1, p2], -self.o[i, q], -self.o[i + 1, q]])
        if 'noreapply_full' in sym:
            # MINIMUM-PRESERVING (not valid for exact-size / pinned-prefix claims): no step reads a node g together with
            # one of g's own fanins. A gate h = op(x, g) with g = op'(x, y) computes an AND-type function of (x, y) or a
            # literal, so h can be rewired to read (x, y) at equal size; fanin indices strictly decrease, so some
            # minimum circuit has no reapplication.
            for i in self.steps:
                for g in self.steps:
                    if g >= i:
                        continue
                    for p in self.pairs[g]:
                        for x in p:
                            add([-self.s[g, p], -self.s[i, (x, g)]])
        self.x = {}
        self.rows = []
        self.min_preserving = [c for c in ('noreapply_full',) if c in sym]

    def add_reader_caps(self, C):
        """MINIMUM-PRESERVING primary-reader caps (theory/primary_reader_caps.py) for budget B = k on a complete table.
        C[i] = (d, cap if some reader absorbs at 0, cap if some reader absorbs at 1); the conditional caps need
        noreapply_full and a trimmed circuit (alonce), which must be enabled."""
        assert 'noreapply_full' in self.min_preserving
        ABS = {0: (0, 0), 1: (0, 1), 2: (1, 0), 3: (1, 1)}       # OPS index -> absorbing value of operand a, operand b
        for i in range(self.n):
            read = [self.s[st, p] for st in self.steps for p in self.pairs[st] if i in p]
            d, *cond = C[i]
            for c in CardEnc.atmost(read, max(d, 0), vpool=self.pool, encoding=EncType.seqcounter).clauses:
                self.solver.add_clause(c)
            for a, kcap in enumerate(cond):
                if kcap >= d or kcap >= len(read):
                    continue
                flag = self.pool.id(('absorb', i, a))
                for st in self.steps:
                    for p in self.pairs[st]:
                        if i not in p:
                            continue
                        pos = p.index(i)
                        for q in range(4):
                            if ABS[q][pos] == a:
                                self.solver.add_clause([-self.s[st, p], -self.o[st, q], flag])
                for c in CardEnc.atmost(read, max(kcap, 0), vpool=self.pool, encoding=EncType.seqcounter).clauses:
                    self.solver.add_clause([-flag] + list(c))
        self.min_preserving.append('reader_caps')

    def val(self, node, t):
        """Literal or constant (True/False) for node at row t."""
        if node < self.n:
            return bool(t >> node & 1)
        return self.x[node, t]

    def add_row(self, t):
        add = self.solver.add_clause; v = self.pool.id
        for i in self.steps:
            self.x[i, t] = v(('x', i, t))
        for i in self.steps:
            for (j, l) in self.pairs[i]:
                sel = self.s[i, (j, l)]
                for a in (0, 1):
                    for b in (0, 1):
                        cond = [-sel]
                        ok = True
                        for node, bit in ((j, a), (l, b)):
                            lv = self.val(node, t)
                            if isinstance(lv, bool):
                                if lv != bool(bit):
                                    ok = False
                            else:
                                cond.append(-lv if bit else lv)
                        if not ok:
                            continue
                        xi = self.x[i, t]
                        if not (a or b):
                            add(cond + [-xi])
                            continue
                        for q in range(4):
                            add(cond + [-self.o[i, q], xi if op_value(q, a, b) else -xi])
        out = self.x[self.n + self.k - 1, t]
        want = bool(self.target >> t & 1)
        if self.free_inv:
            add([-out, -self.inv] if want else [out, -self.inv])     # inv=1: out = not want
            add([out, self.inv] if want else [-out, self.inv])       # inv=0: out = want
        else:
            add([out] if want else [-out])
        self.rows.append(t)

    def decode(self, model):
        pos = set(l for l in model if l > 0)
        gates = []
        for i in self.steps:
            j, l = next(p for p in self.pairs[i] if self.s[i, p] in pos)
            q = next(q for q in range(4) if self.o[i, q] in pos)
            f4 = sum(op_value(q, a, b) << (a | b << 1) for a in (0, 1) for b in (0, 1))
            gates.append([f4, j, l])
        inv = (1 if self.inv in pos else 0) if self.free_inv else self.inv_fixed
        return gates, [self.n + self.k - 1, inv]


def simulate(n, gates, out):
    one = (1 << (1 << n)) - 1
    vals = [sum(1 << t for t in range(1 << n) if t >> i & 1) for i in range(n)]
    for f4, a, b in gates:
        A, B = vals[a], vals[b]
        r = 0
        for idx, m in ((1, A & ~B), (2, ~A & B), (3, A & B), (0, ~A & ~B)):
            if f4 >> idx & 1:
                r |= m
        vals.append(r & one)
    return vals[out[0]] ^ (one if out[1] else 0)


def sound_lower(n, f):
    """Sound lower bound on the free-NOT binary gate count of a complete table (constants and literals cost 0):
    restrict to essential inputs, then max(m - 1, signed regional bound, free-NOT first-gate bound for m <= 9)."""
    one = (1 << (1 << n)) - 1
    keep = [i for i in range(n) if any((f >> a & 1) != (f >> (a | 1 << i) & 1) for a in range(1 << n) if not a >> i & 1)]
    m = len(keep)
    if m <= 1:
        return 0
    g = sum((f >> sum(((a >> j) & 1) << i for j, i in enumerate(keep)) & 1) << a for a in range(1 << m))
    from signed_region_bounds import Bound
    lb = max(m - 1, m - 1 + Bound(m, g).lower())
    if m <= 9:
        from first_gate_bound import lower as fg_lower
        lb = max(lb, fg_lower(m, g, 1))
    return lb


def reader_caps(n, tt, B):
    from primary_reader_caps import caps
    return caps(n, tt, B, sound_lower)


def exists(n, tt, care, k, solver='cadical195', cegar=True, sym=('alonce', 'colex', 'oplex', 'noreapply'),
           init_rows=4, caps=False, stats=None):
    """Exactly k all-used steps. Returns ('SAT', gates, out) / ('UNSAT', None, None).
    With minimum-preserving options (sym 'noreapply_full', caps=True) an UNSAT answer means only "no minimum circuit of
    size k": valid inside an increasing search from a proved lower bound, never as an exact-size or prefix claim."""
    rows = [t for t in range(1, 1 << n) if care >> t & 1]
    if caps:
        assert care == (1 << (1 << n)) - 1, 'reader caps are for complete tables'
        sym = tuple(dict.fromkeys(tuple(sym) + ('alonce', 'noreapply_full')))
    e = Encoding(n, k, tt, care, solver, sym)
    if caps:
        e.add_reader_caps(reader_caps(n, tt, k))
    try:
        start = rows if not cegar else rows[:init_rows]
        for t in start:
            e.add_row(t)
        while True:
            ok = e.solver.solve()
            if stats is not None:
                st = e.solver.accum_stats() or {}
                stats['conflicts'] = st.get('conflicts', 0)        # cumulative for this solver instance (this k)
                stats['vars'] = max(stats.get('vars', 0), e.solver.nof_vars())
                stats['clauses'] = max(stats.get('clauses', 0), e.solver.nof_clauses())
                stats['cegar_rows'] = len(e.rows)
            if not ok:
                return 'UNSAT', None, None
            gates, out = e.decode(e.solver.get_model())
            f = simulate(n, gates, out)
            bad = (f ^ tt) & care
            if not bad:
                return 'SAT', gates, out
            t = (bad & -bad).bit_length() - 1
            assert t not in e.rows, (t, e.rows)
            e.add_row(t)
    finally:
        e.solver.delete()


def minimum(n, tt, care=None, start=1, kmax=64, solver='cadical195', cegar=True, on_step=None, **kw):
    if care is None:
        care = (1 << (1 << n)) - 1
    """Increasing exact-k search from `start`, which must be a proved lower bound. Per-budget stats in 'budgets'."""
    t0 = time.perf_counter(); budgets = []
    for k in range(max(start, 1), kmax + 1):
        tk = time.perf_counter(); stk = {}
        st, gates, out = exists(n, tt, care, k, solver, cegar, stats=stk, **kw)
        budgets.append(dict(k=k, status=st, seconds=round(time.perf_counter() - tk, 4), **stk))
        if on_step:
            on_step(k, st, time.perf_counter() - tk)
        if st == 'SAT':
            return dict(steps=k, gates=gates, out=out, seconds=time.perf_counter() - t0, budgets=budgets)
    return dict(steps=None, seconds=time.perf_counter() - t0, budgets=budgets)


if __name__ == '__main__':
    # quick self-check against known AIG minima
    for n, tt, want in ((3, 0x96, 6), (2, 0x6, 3), (3, 0xE8, 4), (4, 0x6996, 9), (3, 0x80, 2)):
        r = minimum(n, tt, start=1)
        assert r['steps'] == want and simulate(n, r['gates'], r['out']) == tt, (n, hex(tt), r)
        print(n, hex(tt), r['steps'], round(r['seconds'], 3))
