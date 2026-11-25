"""Counted-NOT lower bound for partial (and complete) labels: binary + NOT.

counted_lower(n, P, N) = partial_first_gate_bound.bound(n, P, N, mono=False)    (binary gates; free-NOT)
                       + partial_inversion.inversion(boundary rows)              (exact minimum NOT count)
Binary and NOT gates are disjoint, so the sum bounds the counted total of any AND/OR/NOT circuit consistent
with the labels. Status: provisional (both parts from the independent theory audit); independently tested
against counted gate-set enumeration on every 3-input partial table and 3,000 sampled 4-input tables with no
violation (experiments/partial_not_bound.py): exact on 92% (n = 3) and 76% (n = 4, checked) of tables.
P, N: disjoint bitsets of assignments (bit a = row a)."""
from module_contraction import vars
from partial_first_gate_bound import bound
from partial_inversion import inversion, boundary


def counted_lower(n, P, N):
    if not P or not N:
        return 0
    b = bound(n, P, N, False, True)
    return b + inversion(boundary(vars(n), P, N))


def monotone_lower(n, P, N):
    """Monotone-basis binary bound for partial labels (first-gate elimination)."""
    if not P or not N:
        return 0
    return bound(n, P, N, True, True)
