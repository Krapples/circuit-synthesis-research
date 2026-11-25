"""Adapter so the regional prototypes (phase-first, axis lift) call the production regional completion.
local_cover(...) maps to regional_block_completion.local_blocks with the current recommended opt-in flags
(port_first, witness_cover, row_quotient: the 'row-quotient' completion mode). check_tree is the production
independent witness check (experiments/regional_completion_check.check_tree), restated here so theory/ does not
import experiments/."""
from collections import Counter
from module_contraction import vars as truth_variables
from regional_block_completion import local_blocks
from two_sharing_core import ANY

PRODUCTION_FLAGS = dict(port_first=True, witness_cover=True, row_quotient=True)


def local_cover(m, ports, pats, targets, signed, stats=None, module_filter=True, method=None, port_first=None, **_):
    return local_blocks(m, ports, pats, targets, signed, stats, module_filter, **PRODUCTION_FLAGS)


def check_tree(tree, m, ports, pats, targets, signed):
    counts = Counter(); one = (1 << (1 << m)) - 1

    def walk(node):
        if node[0] == 'x':
            counts[node[1]] += 1
            assert signed or not node[2]
        else:
            for child in node[1:]:
                walk(child)

    def value(node, mask):
        if node[0] == 'x':
            _, i, neg = node
            column = truth_variables(m)[i] if i < m else one if mask >> (i - m) & 1 else 0
            return column ^ (one if neg else 0)
        vals = [value(c, mask) for c in node[1:]]
        out = vals[0]
        for v in vals[1:]:
            out = out & v if node[0] == '&' else out | v
        return out

    walk(tree)
    assert counts == Counter((*range(m), *(m + i for i in ports)))
    assert all(t == ANY or value(tree, p) == t for p, t in zip(pats, targets))
