"""Finite check of the restriction-excess inequality on all 4-input functions.

Claim (free-NOT AIG size C): if every input fixed by rho is essential in f and f|rho is
nonconstant, then C(f) >= C(f|rho) + |dom rho|.  Uses the exact NPN-class sizes in
results/sat_gadget/npn4_exact_aig_all.json (open classes give only bounds and are skipped
only if they could matter).  Run from sat-search:  python -I experiments/excess_restriction_check.py
"""
import json, itertools, pathlib
ROOT = pathlib.Path(__file__).resolve().parent.parent
D = json.load(open(ROOT / 'results/sat_gadget/npn4_exact_aig_all.json'))
PERMS = list(itertools.permutations(range(4)))

def transform(t, p, m, o):
    r = 0
    for x in range(16):
        y = 0
        for i in range(4):
            y |= (((x >> i) & 1) ^ ((m >> i) & 1)) << p[i]
        r |= (((t >> y) & 1) ^ o) << x
    return r

canon = {}
def npn(t):
    if t not in canon:
        canon[t] = min(transform(t, p, m, o) for p in PERMS for m in range(16) for o in (0, 1))
    return canon[t]

def bounds(t):
    e = D['%04x' % npn(t)]
    up = e['upper']; lo = up if e['open_budget'] is None else e['open_budget']
    return lo, up

def supp(t):
    return [i for i in range(4) if any(((t >> x) & 1) != ((t >> (x ^ (1 << i))) & 1) for x in range(16))]

def restrict(t, i, b):
    r = 0
    for x in range(16):
        y = (x & ~(1 << i)) | (b << i)
        r |= ((t >> y) & 1) << x
    return r

checked = viol = undecided = 0
for t in range(1 << 16):
    s = supp(t)
    lo_f, up_f = bounds(t)
    for k in range(1, len(s) + 1):
        for dom in itertools.combinations(s, k):
            for vals in itertools.product((0, 1), repeat=k):
                g = t
                for i, b in zip(dom, vals):
                    g = restrict(g, i, b)
                if g in (0, 0xffff):
                    continue
                lo_g, up_g = bounds(g)
                checked += 1
                if lo_f >= up_g + k:
                    continue
                if up_f < lo_g + k:
                    viol += 1; print('VIOLATION', hex(t), dom, vals)
                else:
                    undecided += 1
assert all(('%04x' % npn(int(k, 16))) == k for k in D), 'keys are not NPN minima'
print(json.dumps({'checked': checked, 'violations': viol, 'undecided': undecided}))
