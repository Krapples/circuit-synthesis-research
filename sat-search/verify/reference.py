"""Independent exact reference for small circuit-synthesis instances.

This module shares no code with cube_search.py and applies no pruning, symmetry breaking or implied
constraints. It answers one question exactly:

    exists(n, tt, G, basis, prefix, all_read): is there a straight-line program with exactly G gates over
    inputs x0..x{n-1}, each gate AND/OR of two distinct earlier wires (or NOT of one earlier wire when
    basis == 'general'), whose last gate computes the truth table tt, whose first len(prefix) gates are the
    given prefix, and (if all_read) in which every wire except the output is read by some gate?

This is the model used by the cube_search exact-G encoding (wires n..n+G-1, l < r for binary gates, every
wire read). Two backends implement it:
  * brute_exists: plain enumeration of gate sequences (tiny instances), used to validate the SAT backend;
  * sat_exists: a direct CNF (one selector per (op, operands) choice, all 2^n rows, no extra clauses).
Witnesses are evaluated on every row before being returned.

Input contracts (normalize_terms / graph_terms) reject or normalize malformed families: duplicate or
reversed edges, self-loops, vertices out of range, empty terms, non-minimal terms."""
import os, sys
from itertools import combinations
# python-sat is vendored in <repo>/.scratch-sat (README setup)
sys.path.append(os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), '.scratch-sat'))
from pysat.formula import IDPool
from pysat.solvers import Solver

AND, OR, NOT = 0, 1, 2


# ---------------------------------------------------------------- input contracts

def normalize_terms(n, terms):
    """Validated, deduplicated antichain of minimal terms (bitmasks over n inputs) of a monotone DNF."""
    if not isinstance(n, int) or n < 1:
        raise ValueError(f'n must be a positive integer, got {n!r}')
    clean = set()
    for t in terms:
        if not isinstance(t, int) or t <= 0:
            raise ValueError(f'term {t!r} must be a positive bitmask')
        if t >> n:
            raise ValueError(f'term {t:#x} uses an input >= n = {n}')
        clean.add(t)
    if not clean:
        raise ValueError('empty family (constant-0 function)')
    return tuple(sorted(t for t in clean if not any(o != t and o & t == o for o in clean)))


def graph_terms(n, edges):
    """Edge terms of a simple graph: rejects self-loops and out-of-range vertices, merges duplicates."""
    out = set()
    for e in edges:
        u, v = e
        if not (0 <= u < n and 0 <= v < n):
            raise ValueError(f'edge {e} has a vertex outside 0..{n - 1}')
        if u == v:
            raise ValueError(f'self-loop {e} is not a graph edge')
        out.add((1 << u) | (1 << v))
    return normalize_terms(n, out)


def truth_table(n, terms):
    """Bit x of the result is f(x) for the monotone DNF with the given terms."""
    return sum(1 << x for x in range(1 << n) if any(x & t == t for t in terms))


def essential_inputs(n, tt):
    return [i for i in range(n) if any((tt >> x & 1) != (tt >> (x ^ (1 << i)) & 1) for x in range(1 << n))]


def evaluate(n, gates, x):
    v = [x >> i & 1 for i in range(n)]
    for op, a, b in gates:
        v.append(v[a] & v[b] if op == AND else v[a] | v[b] if op == OR else 1 - v[a])
    return v[-1]


def check_witness(n, tt, gates, prefix=(), all_read=True, basis='monotone'):
    """Independent validation of a returned circuit against the model."""
    if tuple(map(tuple, gates[:len(prefix)])) != tuple(map(tuple, prefix)):
        return False
    for j, (op, a, b) in enumerate(gates, n):
        if op == NOT:
            if basis != 'general' or a != b or not 0 <= a < j:
                return False
        elif op in (AND, OR):
            if not 0 <= a < b < j:
                return False
        else:
            return False
    if all_read:
        read = set()
        for op, a, b in gates:
            read.update((a, b))
        if any(w not in read for w in range(n + len(gates) - 1)):
            return False
    return all(evaluate(n, gates, x) == (tt >> x & 1) for x in range(1 << n))


def options(j, basis):
    """All gate choices for wire j."""
    out = [(op, a, b) for b in range(j) for a in range(b) for op in (AND, OR)]
    if basis == 'general':
        out += [(NOT, a, a) for a in range(j)]
    return out


# ---------------------------------------------------------------- brute force (tiny instances)

def brute_exists(n, tt, G, basis='monotone', prefix=(), all_read=True):
    """Enumerate every gate sequence; returns a witness or None. Only pruning: the unread-wire count,
    which cannot exceed the operand slots left (2 per remaining gate) -- a counting fact, not a rule."""
    if G < len(prefix) or G < 1:
        return None
    full = (1 << (1 << n)) - 1
    cols = [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]
    gates = []

    def apply(op, a, b, vals):
        return vals[a] & vals[b] if op == AND else vals[a] | vals[b] if op == OR else full ^ vals[a]

    def rec(vals, unread):
        j = len(vals)
        left = n + G - j
        if left == 0:
            if vals[-1] == tt and (not all_read or not (unread - {j - 1})):
                return list(gates)
            return None
        if all_read and len(unread) > 2 * left + 1:   # the output itself may stay unread
            return None
        k = j - n
        for op, a, b in ([prefix[k]] if k < len(prefix) else options(j, basis)):
            gates.append((op, a, b))
            r = rec(vals + [apply(op, a, b, vals)], (unread - {a, b}) | {j})
            gates.pop()
            if r is not None:
                return r
        return None

    return rec(cols, set(range(n)))


# ---------------------------------------------------------------- direct SAT encoding

def sat_exists(n, tt, G, basis='monotone', prefix=(), all_read=True, solver='glucose4', proof=False,
               seconds=None):
    """Returns (witness or None, info). info has clause/variable counts and, with proof=True and a solver
    supporting it, the DRUP proof lines of an UNSAT answer together with the CNF."""
    if G < max(1, len(prefix)):
        return None, dict(trivial=True)
    pool = IDPool()
    cnf = []
    out = n + G - 1
    rows = range(1 << n)

    def val(w, x):
        return pool.id(('v', w, x))

    choice = {}
    for j in range(n, out + 1):
        opts = options(j, basis)
        k = j - n
        if k < len(prefix):
            if tuple(prefix[k]) not in opts:
                return None, dict(trivial=True, reason=f'prefix gate {prefix[k]} invalid at wire {j}')
            opts = [tuple(prefix[k])]
        if not opts:
            return None, dict(trivial=True, reason=f'no gate choice at wire {j}')
        choice[j] = {o: pool.id(('c', j, o)) for o in opts}
        lits = list(choice[j].values())
        cnf.append(lits)                                          # exactly one choice: pairwise encoding
        cnf.extend([-p, -q] for p, q in combinations(lits, 2))

    def lit(w, x):
        """Literal for wire w on row x; inputs are constants (None means true/false handled by caller)."""
        return val(w, x)

    for x in rows:
        for i in range(n):
            cnf.append([val(i, x)] if x >> i & 1 else [-val(i, x)])
        for j, ch in choice.items():
            f = val(j, x)
            for (op, a, b), c in ch.items():
                va, vb = lit(a, x), lit(b, x)
                if op == AND:
                    cnf += [[-c, -va, -vb, f], [-c, va, -f], [-c, vb, -f]]
                elif op == OR:
                    cnf += [[-c, va, vb, -f], [-c, -va, f], [-c, -vb, f]]
                else:
                    cnf += [[-c, -va, -f], [-c, va, f]]
        cnf.append([val(out, x)] if tt >> x & 1 else [-val(out, x)])
    if all_read:
        for w in range(out):
            readers = [c for j, ch in choice.items() if j > w for (op, a, b), c in ch.items() if w in (a, b)]
            cnf.append(readers)
    info = dict(vars=pool.top, clauses=len(cnf), solver=solver)
    with Solver(name=solver, bootstrap_with=cnf, with_proof=proof) as s:
        if seconds is None:
            ok = s.solve()
        else:                       # time-limited: None means undecided (never treated as UNSAT)
            import threading
            timer = threading.Timer(seconds, s.interrupt)
            timer.start()
            ok = s.solve_limited(expect_interrupt=True)
            timer.cancel()
            if ok is None:
                info['undecided'] = True
                return None, info
        if not ok:
            if proof:
                info['proof'] = s.get_proof()
                info['cnf'] = cnf
            return None, info
        model = set(l for l in s.get_model() if l > 0)
    gates = []
    for j, ch in choice.items():
        sel = [o for o, c in ch.items() if c in model]
        assert len(sel) == 1
        gates.append(sel[0])
    if not check_witness(n, tt, gates, prefix, all_read, basis):
        raise AssertionError(f'reference SAT returned an invalid circuit {gates}')
    return gates, info


def minimum(n, tt, basis='monotone', prefix=(), all_read=True, Gmax=None, backend=sat_exists, seconds=None):
    """Smallest G with an exact-G circuit (None if none up to Gmax). With all_read the search starts at the
    counting floor n + G - 1 <= 2G (every non-output wire needs a reader slot) for binary-only bases."""
    lo = max(1, len(prefix))
    if all_read and basis == 'monotone':
        lo = max(lo, n - 1)
    Gmax = Gmax if Gmax is not None else 4 * n + len(prefix)
    for G in range(lo, Gmax + 1):
        r = backend(n, tt, G, basis, prefix, all_read, seconds=seconds) if seconds else             backend(n, tt, G, basis, prefix, all_read)
        if isinstance(r, tuple) and r[1].get('undecided'):
            return 'undecided', None
        w = r[0] if isinstance(r, tuple) else r
        if w is not None:
            return G, w
    return None, None
