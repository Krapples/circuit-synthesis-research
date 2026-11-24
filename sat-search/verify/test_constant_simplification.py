"""Order of operations in the distinction-gap reduction (NOTES_SYNTHESIS_FOLLOWUP, 'Computing the gap and
reducing the core inputs'): fixing single-polarity inputs to constants and simplifying must use only edge
deletions (a gate that becomes constant is deleted, its dead cone removed) and edge contractions (a gate that
becomes a copy of one operand is merged into it; an idempotent gate on a doubled operand likewise). Cycle rank
E - V + C never increases under deletion or contraction (standard graph fact), and for an every-wire-read
circuit with one output it equals the sharing B - m + 1, so the certificate lemma's sharing budget survives
the simplification. Representative relocation (replacing an input by an owner that is already read)
identifies two vertices and can raise the cycle rank, so the lemma must be applied before relocation.

Checks, exhaustive over every every-wire-read program of 1..4 gates on 2..3 inputs in both bases, for every
input and constant: the simplified circuit computes the restriction, every remaining wire is read, and its
cycle rank does not exceed the original's. Plus an explicit relocation example that raises the rank.
These are finite tests of the stated invariant (the invariant itself follows from minor monotonicity).
Run: python verify/test_constant_simplification.py"""
import os, sys, unittest
from itertools import combinations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import reference as ref

AND, OR, NOT = 0, 1, 2


def cycle_rank(n_inputs_used, gates, wires):
    """E - V + C of the undirected multigraph on the given wires (gates: (op, a, b) over wire ids)."""
    parent = {w: w for w in wires}

    def find(w):
        while parent[w] != w:
            parent[w] = parent[parent[w]]
            w = parent[w]
        return w
    E = 0
    for j, (op, a, b) in gates.items():
        for u in ((a,) if op == NOT else (a, b)):
            E += 1
            ru, rj = find(u), find(j)
            if ru != rj:
                parent[ru] = rj
    C = len({find(w) for w in wires})
    return E - len(wires) + C


def all_read_programs(n, B, basis):
    out = []

    def rec(gates, unread):
        j = n + len(gates)
        if len(gates) == B:
            if not (unread - {j - 1}):
                out.append(tuple(gates))
            return
        if len(unread) > 2 * (B - len(gates)) + 1:
            return
        opts = [(op, a, b) for b in range(j) for a in range(b) for op in (AND, OR)]
        if basis == 'general':
            opts += [(NOT, a, a) for a in range(j)]
        for g in opts:
            gates.append(g)
            rec(gates, (unread - {g[1], g[2]}) | {j})
            gates.pop()
    rec([], set(range(n)))
    return out


def simplify(n, gates, x, c):
    """Fix input x = c and simplify by deletions and contractions only. Returns (gates dict over original wire
    ids, output wire, constant) where constant is 0/1 if the restricted output is constant, else None."""
    const = {x: c}
    alias = {}

    def res(w):
        while w in alias:
            w = alias[w]
        return w
    kept = {}
    for j, (op, a, b) in enumerate(gates, n):
        a, b = res(a), res(b)
        if op == NOT:
            if a in const:
                const[j] = 1 - const[a]
            else:
                kept[j] = (NOT, a, a)
            continue
        ca, cb = const.get(a), const.get(b)
        absorbing = 0 if op == AND else 1
        if ca == absorbing or cb == absorbing:
            const[j] = absorbing                              # deletion
        elif ca is not None and cb is not None:
            const[j] = ca if op == AND else (ca | cb)
        elif ca is not None:
            alias[j] = b                                      # contraction onto the other operand
        elif cb is not None:
            alias[j] = a
        elif a == b:
            alias[j] = a                                      # idempotent on a doubled operand: contraction
        else:
            kept[j] = (op, min(a, b), max(a, b))
    out = res(n + len(gates) - 1)
    if out in const:
        return {}, None, const[out]
    # dead-cone removal (deletions)
    live, stack = set(), [out]
    while stack:
        w = stack.pop()
        if w in live:
            continue
        live.add(w)
        if w in kept:
            stack.extend(kept[w][1:])
    return {j: g for j, g in kept.items() if j in live}, out, None


def evaluate(gates, out, assign):
    val = dict(assign)
    for j in sorted(gates):
        op, a, b = gates[j]
        val[j] = val[a] & val[b] if op == AND else val[a] | val[b] if op == OR else 1 - val[a]
    return val[out]


class ConstantSimplification(unittest.TestCase):
    def test_exhaustive_invariant(self):
        checked = 0
        for basis in ('monotone', 'general'):
            for n in (2, 3):
                for B in range(1, 5 if n == 2 else 4):
                    for gates in all_read_programs(n, B, basis):
                        wires0 = set(range(n + B))
                        r0 = cycle_rank(n, dict(enumerate(gates, n)), wires0)
                        self.assertEqual(r0, B - n + 1 - sum(1 for g in gates if g[0] == NOT))
                        for x in range(n):
                            for c in (0, 1):
                                kept, out, k = simplify(n, gates, x, c)
                                for row in range(1 << n):
                                    if (row >> x & 1) != c:
                                        continue
                                    want = ref.evaluate(n, list(gates), row)
                                    got = k if out is None else evaluate(kept, out, {i: row >> i & 1 for i in range(n)})
                                    self.assertEqual(got, want, (gates, x, c, row))
                                if out is None:
                                    continue
                                read = {w for g in kept.values() for w in g[1:]}
                                inputs = {w for w in read if w < n}
                                wires = inputs | set(kept) | ({out} if out < n else set())
                                self.assertTrue(all(w in read for w in wires - {out}), (gates, x, c))
                                self.assertLessEqual(cycle_rank(len(inputs), kept, wires), r0, (gates, x, c))
                                checked += 1
        print(f'\n  {checked} (program, input, constant) simplifications: restriction computed, all wires read, '
              f'cycle rank never increased')
        self.assertGreater(checked, 1000)

    def test_relocation_can_raise_rank(self):
        """OR(AND(x0, x1), x2): rank 0. Relocating x2 to its owner x0 gives OR(AND(x0, x1), x0): rank 1."""
        before = {3: (AND, 0, 1), 4: (OR, 3, 2)}
        after = {3: (AND, 0, 1), 4: (OR, 0, 3)}
        self.assertEqual(cycle_rank(3, before, {0, 1, 2, 3, 4}), 0)
        self.assertEqual(cycle_rank(2, after, {0, 1, 3, 4}), 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
