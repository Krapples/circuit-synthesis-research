"""Mixed-rank cuts: a floor on structurally mixed AND/OR gates for a complete Boolean function.

Source: sat-search/chatgpt_handoff/first_gate_translation_proof_handoff.md (scalar theorem, paper
proof by square-zero first-gate induction, 2026-11-26; not Lean checked) with the sharp rank-one
chain from mixed_dependency_rank_handoff.md.

Theorem used (scalar, proven on paper): split the inputs into a side X and its complement Q. Let
H_f(x, q) = f(x, q) + f(x, 0) + f(0, q) + f(0, 0) over GF(2) and R(f, X) the GF(2) rank of the
matrix H_f. If a circuit with free affine wiring computes f and t of its AND gates are syntactically
mixed (pure-side gates have no mixed ancestors; pure-side preprocessing is arbitrary), then
R(f, X) <= 2^(t+1) - 2 for t >= 1, and R = 0 for t = 0. Hence t >= floor(R) := bitlen(R + 1) - 1.

Scope in this repository:
  * Basis AND/OR/NOT with fan-in <= 2 (cube_search.build). AND and OR are AND gates up to input and
    output negation; NOT is affine. A gate is mixed when it structurally reads inputs from both
    sides; the structural classification is a valid syntactic partition (pure gates read only one
    side). So every AND/OR/NOT circuit for f has at least floor(R(f, X)) AND/OR gates that read
    both sides, for every X. Structural dependence over-approximates semantic dependence, which
    only increases the count.
  * Complete functions only. A partial specification has an unknown completion rank, so the floor
    is not applied to partial labels.
  * The joint (multi-output) ceiling is a conjecture and is not used.

Rank is invariant under negating inputs or the output and under permuting inputs within a side.
Inputs that are pairwise symmetric in f form classes; a cut's rank depends only on how many inputs
of each class lie on each side, which is the cache key (symmetry reduction).
"""
from functools import lru_cache
from itertools import product

from pysat.card import CardEnc


def mixed_floor(rank):
    """Least t with 2^(t+1) - 2 >= rank (0 for rank 0)."""
    return (rank + 1).bit_length() - 1


def gf2_rank(rows):
    """Rank over GF(2) of integer bit rows (xor basis keyed by leading bit)."""
    basis = {}
    for r in rows:
        while r:
            top = r.bit_length() - 1
            b = basis.get(top)
            if b is None:
                basis[top] = r
                break
            r ^= b
    return len(basis)


def _cofactor_index(n, positions):
    """For each pattern p over `positions` (bit k of p sets input positions[k]), the row index."""
    out = []
    for p in range(1 << len(positions)):
        x = 0
        for k, v in enumerate(positions):
            if p >> k & 1:
                x |= 1 << v
        out.append(x)
    return out


def anchored_mixed_rank(n, truth, side):
    """GF(2) rank of H_f(x, q) for side mask X = side (inputs not in side form Q)."""
    xs = [v for v in range(n) if side >> v & 1]
    qs = [v for v in range(n) if not side >> v & 1]
    if not xs or not qs:
        return 0
    xi, qi = _cofactor_index(n, xs), _cofactor_index(n, qs)
    bit = lambda r: truth >> r & 1
    f0q = [bit(q) for q in qi]
    f00 = f0q[0]
    rows = []
    for x in xi[1:]:
        fx0 = bit(x)
        row = 0
        for k, q in enumerate(qi):
            if bit(x | q) ^ fx0 ^ f0q[k] ^ f00:
                row |= 1 << k
        rows.append(row)
    return gf2_rank(rows)


def essential_inputs(n, truth):
    full = (1 << (1 << n)) - 1
    ess = []
    for v in range(n):
        lo = sum(1 << r for r in range(1 << n) if not r >> v & 1)
        lo_part = truth & lo
        hi_part = (truth >> (1 << v)) & lo
        if lo_part != hi_part:
            ess.append(v)
    return ess


def _swap_table(n, truth, u, v):
    out = 0
    for r in range(1 << n):
        if truth >> r & 1:
            bu, bv = r >> u & 1, r >> v & 1
            s = r & ~((1 << u) | (1 << v)) | (bv << u) | (bu << v)
            out |= 1 << s
    return out


def symmetry_classes(n, truth, inputs):
    """Partition `inputs` into classes of pairwise swap-symmetric variables (transitive closure)."""
    classes = []
    for v in inputs:
        for c in classes:
            if _swap_table(n, truth, c[0], v) == truth:
                c.append(v)
                break
        else:
            classes.append([v])
    return classes


@lru_cache(maxsize=4096)
def cut_floors(n, truth, use_symmetry=True):
    """All proper cuts of the essential inputs with floor >= 1, as (floor, rank, side_mask).

    One representative per complementary pair (the side holding the lowest essential input).
    Inessential inputs never matter and are left on the Q side. With use_symmetry, ranks are
    cached per class-count vector, so equivalent cuts are ranked once.
    """
    ess = essential_inputs(n, truth)
    if len(ess) < 2:
        return ()
    classes = symmetry_classes(n, truth, ess) if use_symmetry else [[v] for v in ess]
    cache, out, ranked = {}, [], 0
    first = ess[0]
    rest = [v for v in ess if v != first]
    for bits in product((0, 1), repeat=len(rest)):
        side = 1 << first
        for b, v in zip(bits, rest):
            if b:
                side |= 1 << v
        if side == sum(1 << v for v in ess):
            continue
        key = tuple(sum(side >> v & 1 for v in c) for c in classes)
        if key not in cache:
            cache[key] = anchored_mixed_rank(n, truth, side)
            ranked += 1
        r = cache[key]
        if r:
            out.append((mixed_floor(r), r, side))
    out.sort(key=lambda c: (-c[0], -c[1], c[2]))
    return tuple(out)


def select_cuts(n, truth, limit=8, min_floor=2):
    """Strongest cuts, at most one per distinct floor-side pattern, floor >= min_floor."""
    return [c for c in cut_floors(n, truth) if c[0] >= min_floor][:limit]


def structural_mixed_counts(n, gates, output, side):
    """Count AND/OR gates in the output cone that read both sides (witness gates: op 0/1/2)."""
    reads = {v: (1 << v) for v in range(n)}
    for j, (op, a, b) in enumerate(gates, start=n):
        reads[j] = reads[a] | (reads[b] if op != 2 else 0)
    cone, stack = set(), [output]
    while stack:
        w = stack.pop()
        if w in cone or w < n:
            continue
        cone.add(w)
        op, a, b = gates[w - n]
        stack.extend((a,) if op == 2 else (a, b))
    full = (1 << n) - 1
    return sum(1 for j in cone if gates[j - n][0] != 2 and reads[j] & side and reads[j] & full & ~side)


def add_mixed_rank_cuts(n, output, pool, ops, select, clauses, cuts, cone_root=None):
    """CNF: at least floor AND/OR gates read both sides of each cut.

    ops[j] = (and, or, not) literals and select[j, k][i] the operand selectors of cube_search.build.
    Exact-size callers (every wire used, output wire fixed) pass cone_root=None: every gate is in the
    output cone. Padded callers pass cone_root = list of output-selector literals (one per wire); the
    count is then restricted to gates in the selected output's cone.
    """
    gates = sorted(ops)
    cone = None
    if cone_root is not None:
        cone = {j: pool.id(('mr_cone', j)) for j in gates}
        for j in gates:
            clauses.append([-cone_root[j], cone[j]])
        support = {i: [cone_root[i]] for i in gates}
        for j in gates:
            for k in range(2):
                for i, sel in enumerate(select[j, k]):
                    if i in cone:
                        clauses.append([-cone[j], -sel, cone[i]])
                        use = pool.id(('mr_cone_use', j, k, i))
                        clauses.extend(([-use, cone[j]], [-use, sel]))
                        support[i].append(use)
        # Least fixpoint: a gate is in the cone only if it is the output or a cone gate reads it.
        for i in gates:
            clauses.append([-cone[i], *support[i]])
    for floor, _rank, side in cuts:
        pure = {}
        for s, label in ((side, 'X'), (None, 'Q')):
            p = {i: pool.id(('mr_pure', side, label, i)) for i in range(output + 1)}
            for i in range(n):
                on_x = bool(side >> i & 1)
                clauses.append([p[i]] if (on_x if label == 'X' else not on_x) else [-p[i]])
            for j in gates:
                a = [pool.id(('mr_arg', side, label, j, k)) for k in range(2)]
                for k in range(2):
                    for i, sel in enumerate(select[j, k]):
                        clauses.extend(([-sel, -a[k], p[i]], [-sel, a[k], -p[i]]))
                # NOT reads operand 0 only (operand 1 equals operand 0 under the encoding).
                clauses.extend(([-p[j], a[0]], [-p[j], a[1]], [p[j], -a[0], -a[1]]))
            pure[label] = p
        mixed = []
        for j in gates:
            m = pool.id(('mr_mixed', side, j))
            clauses.extend(([-m, -pure['X'][j]], [-m, -pure['Q'][j]], [-m, -ops[j][2]]))
            if cone is not None:
                clauses.append([-m, cone[j]])
            mixed.append(m)
        if floor > len(mixed):
            clauses.append([])
        else:
            clauses.extend(CardEnc.atleast(mixed, bound=floor, vpool=pool).clauses)
