#!/usr/bin/env python3
"""Replay for translation_doubling_handoff.md.

Checks, on deterministic random generic templates
    G_i = (z_{2i-1} + alpha_i . pool_<i)(z_{2i} + beta_i . pool_<i),  pool = earlier gates + m extra inputs,
the following exact statements (truth tables over GF(2), modules closed under all unit translations):

 S1  scalar first-gate identity   rho(H) = rho(H') + 2 dim Delta_y R H'      (H = lambda.G, H' = H with z1 z2 -> y)
 S2  scalar ceiling               rho(lambda.G) <= 2^(t+1)   (hence R_mix <= 2^(t+1)-2), tight on monomials
 S3  family first-gate identity   dim R F = dim R F' + 2 dim Delta_y R F', and the same for m R F
 S4  joint conjecture (open)      mu(F) <= 2^(t+1)-1 and the open part-2 bound dim Delta_v R F <= 2^t
 S5  subgroup invariant (open for Z-touching V): dim m_V R F <= 2^(t+1) - 2^(t+1-dim V)
 S6  composition                  dim R F[y:=h] = dim R F + (rho(h)-2) dim Delta_y R F, h nonconstant on fresh variables
 S7  square-zero halving          dim Delta_v M <= dim M / 2 for every checked module M and direction v
 C1  negative control: joint rank exceeds every single-output mixed rank on some templates
Sampled checks are evidence, not proof; S1, S3, S6, S7 are proved in the handoff and replayed here.
Usage: python -B translation_doubling_check.py [seed]
"""
import random, sys

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20261126
rnd = random.Random(SEED)


class Space:
    def __init__(s, n):
        s.n = n
        N = 1 << n
        s.full = (1 << N) - 1
        s.M0, s.V = [], []
        for k in range(n):
            blk = (1 << (1 << k)) - 1
            per = 1 << (k + 1)
            m = 0
            for st in range(0, N, per):
                m |= blk << st
            s.M0.append(m)
            s.V.append(s.full ^ m)  # truth table of variable k

    def sh(s, f, k):
        b = 1 << k
        m = s.M0[k]
        return ((f & m) << b) | ((f >> b) & m)

    def shv(s, f, v):
        for k in range(s.n):
            if v >> k & 1:
                f = s.sh(f, k)
        return f


def red(p, x):
    while x:
        q = p.get(x.bit_length() - 1)
        if q is None:
            return x
        x ^= q
    return 0


def add(p, x):
    x = red(p, x)
    if x:
        p[x.bit_length() - 1] = x
    return x


def module(S, fs):
    p, st = {}, []
    for f in fs:
        if add(p, f):
            st.append(f)
    while st:
        f = st.pop()
        for k in range(S.n):
            d = f ^ S.sh(f, k)
            if add(p, d):
                st.append(d)
    return p


def mdim(S, p, dirs=None):
    dirs = [1 << k for k in range(S.n)] if dirs is None else dirs
    q = {}
    for f in p.values():
        for v in dirs:
            add(q, f ^ S.shv(f, v))
    return len(q)


def ddir(S, p, v):
    q = {}
    for f in p.values():
        add(q, f ^ S.shv(f, v))
    return len(q)


def gates(S, t, m, deps, first=None, offset=0):
    """deps[i] = (amask, bmask) over pool = earlier gates + extras.
    Variables: z_1..z_2t at offset.., extras after.  If first is given, G1 := first and z1,z2 absent
    (substituted space: index 0 is y, z3.. start at 1)."""
    G = []
    if first is None:
        zi = lambda j: S.V[j]
        Y = S.V[2 * t:2 * t + m]
    else:
        zi = lambda j: S.V[j - 1]
        Y = S.V[2 * t - 1:2 * t - 1 + m]
    for i in range(t):
        if i == 0 and first is not None:
            G.append(first)
            continue
        pool = G + Y
        a, b = zi(2 * i), zi(2 * i + 1)
        am, bm = deps[i]
        for j, g in enumerate(pool):
            if am >> j & 1:
                a ^= g
            if bm >> j & 1:
                b ^= g
        G.append(a & b)
    return G


def rand_deps(t, m):
    return [(rnd.getrandbits(i + m), rnd.getrandbits(i + m)) for i in range(t)]


def comb(G, lam):
    h = 0
    for i, g in enumerate(G):
        if lam >> i & 1:
            h ^= g
    return h


stats = {}
def tick(k, n=1):
    stats[k] = stats.get(k, 0) + n


def fail(msg):
    print("FAIL", msg)
    sys.exit(1)


CONFIGS = [(1, 2, 40), (2, 2, 60), (3, 2, 60), (3, 3, 30), (4, 2, 25), (4, 3, 8)]
tight_scalar = {}
tight_joint = {}
excess_hist = {}
gens = {}
for t, m, trials in CONFIGS:
    n = 2 * t + m
    S, Sp = Space(n), Space(n - 1)
    for _ in range(trials):
        deps = rand_deps(t, m)
        # G1 = z1 z2 has empty pool masks by construction only if we force them: first gate has pool = extras.
        # Extras feed G1 too; the substitution needs G1 = z1 z2 exactly, so clear deps[0] for S1/S3/S6.
        deps0 = [(0, 0)] + deps[1:]
        G = gates(S, t, m, deps0)
        Gp = gates(Sp, t, m, deps0, first=Sp.V[0])
        y = 1  # direction of y in substituted space
        # S3 family identity
        RF, RFp = module(S, G), module(Sp, Gp)
        mu, mup = mdim(S, RF), mdim(Sp, RFp)
        if len(RF) != len(RFp) + 2 * ddir(Sp, RFp, y):
            fail(("S3", t, m, deps0))
        if mu != mup + 2 * ddir(Sp, RFp, y):
            fail(("S3m", t, m, deps0))
        gens[(t, len(RF) - mu)] = gens.get((t, len(RF) - mu), 0) + 1
        tick("S3 family identity")
        # S7 halving on both modules, all unit and random directions
        for P, SS in ((RF, S), (RFp, Sp)):
            for v in list(1 << k for k in range(SS.n)) + [rnd.randrange(1, 1 << SS.n) for _ in range(4)]:
                if 2 * ddir(SS, P, v) > len(P):
                    fail(("S7", t, m))
                tick("S7 halving")
        # S1/S2 scalar
        for lam in rnd.sample(range(1, 1 << t), min((1 << t) - 1, 6)):
            H, Hp = comb(G, lam), comb(Gp, lam)
            RH, RHp = module(S, [H]), module(Sp, [Hp])
            if len(RH) != len(RHp) + 2 * ddir(Sp, RHp, y):
                fail(("S1", t, m, deps0, lam))
            tick("S1 scalar identity")
            if len(RH) > 2 ** (t + 1):
                fail(("S2", t, m, deps, lam))
            tick("S2 scalar ceiling")
            tight_scalar[t] = max(tight_scalar.get(t, 0), len(RH))
        # S4/S5 on full random deps (G1 may read extras)
        G = gates(S, t, m, deps)
        RF = module(S, G)
        mu = mdim(S, RF)
        if mu > 2 ** (t + 1) - 1:
            print("VIOLATION S4 mu", t, m, deps); sys.exit(2)
        tick("S4 joint ceiling (sampled)")
        tight_joint[t] = max(tight_joint.get(t, 0), mu)
        for v in list(1 << k for k in range(n)) + [rnd.randrange(1, 1 << n) for _ in range(6)]:
            if ddir(S, RF, v) > 2 ** t:
                print("VIOLATION S4 direction", t, m, deps, v); sys.exit(2)
            tick("S4 part-2 directions (sampled)")
        for k in range(1, min(n, 4) + 1):
            V = [rnd.randrange(1, 1 << n) for _ in range(k)]
            # span dimension of V
            pv = {}
            for v in V:
                add(pv, v)
            kk = len(pv)
            span = [0]
            for v in pv.values():
                span += [x ^ v for x in span]
            d = mdim(S, RF, [w for w in span if w])
            if d > 2 ** (t + 1) - 2 ** (t + 1 - kk):
                print("VIOLATION S5", t, m, deps, V); sys.exit(2)
            tick("S5 subgroup invariant (sampled)")
        # C1 histogram: J - max_lambda R_mix(lambda.G)
        best = max(len(module(S, [comb(G, l)])) for l in range(1, 1 << t))
        ex = (mu - 1) - (best - 2)
        excess_hist[(t, ex)] = excess_hist.get((t, ex), 0) + 1

# tightness on monomial chains: G_i = (z + G_{i-1}) z'  gives degree t+1 product structure
for t in range(1, 5):
    S = Space(2 * t)
    deps = [(0, 0)] + [(1 << (i - 1), 0) for i in range(1, t)]
    G = gates(S, t, 0, deps)
    r = len(module(S, [G[-1]]))
    if r != 2 ** (t + 1):
        fail(("tight", t, r))
    tick("S2 tightness chains")

# S6 composition with h on fresh disjoint variables
for t, m, trials in [(2, 2, 30), (3, 1, 20)]:
    for _ in range(trials):
        hv = 3
        n0 = 2 * t + m
        S = Space(n0 + hv)
        deps = rand_deps(t, m)
        G = gates(S, t, m, deps)
        h = rnd.getrandbits(1 << hv)
        # extend h to the big space as function of the last hv variables
        hfun = 0
        for k in range(1 << hv):
            if h >> k & 1:
                term = S.full
                for b in range(hv):
                    term &= S.V[n0 + b] if k >> b & 1 else S.full ^ S.V[n0 + b]
                hfun |= term
        if hfun in (0, S.full):
            continue
        ycol = 2 * t  # first extra input plays y
        # F[y:=h]: rebuild with V[ycol] replaced
        save = S.V[ycol]
        S.V[ycol] = hfun
        Gs = gates(S, t, m, deps)
        S.V[ycol] = save
        RF0 = module(S, G)
        lhs = len(module(S, Gs))
        rhs = len(RF0) + (len(module(S, [hfun])) - 2) * ddir(S, RF0, 1 << ycol)
        if lhs != rhs:
            fail(("S6", t, m, deps, h, lhs, rhs))
        tick("S6 composition")

if not any(ex > 0 for (t, ex) in excess_hist):
    fail("C1 expected a joint excess")
print("seed", SEED)
for k in sorted(stats):
    print(f"{k}: {stats[k]}")
print("max scalar rho by t:", dict(sorted(tight_scalar.items())), "(ceiling 2^(t+1))")
print("max joint mu by t:", dict(sorted(tight_joint.items())), "(conjectured ceiling 2^(t+1)-1)")
print("generator count dim RF - dim mRF (t, g): count", dict(sorted(gens.items())))
print("C1 histogram (t, J - max single R_mix): count", dict(sorted(excess_hist.items())))
print("ALL CHECKS PASSED (S4/S5 sampled only; joint conjecture remains open)")
