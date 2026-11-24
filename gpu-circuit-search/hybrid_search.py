"""Exact circuit-size search: CPU enumerates prefixes, GPU exhausts suffixes.

Decides whether the "some edge has both ends true" function of a graph has a circuit
of AND/OR/NOT gates (fan-in <= 2) with at most S gates. Complete for that question:

* A minimum circuit never has a constant gate, a gate equal to an input, or two gates
  computing the same function (each could be removed). So every minimum circuit's first
  P gates form a set of P distinct, non-trivial functions, each one gate away from the
  inputs and the earlier ones. The CPU builds all such sets level by level (BFS over sets,
  so different gate orders that give the same set are explored once).
* For each level-P set, the GPU tries every way to add the remaining K = S - P gates,
  checking every new gate against the target. Any circuit with <= S gates is found.

Truth tables are 256-bit (4 x uint64) over 8 variables; graphs with n < 8 vertices just
ignore the high variables. A witness is re-checked on the CPU with the Lean semantics.

Usage: python hybrid_search.py --n 8 --edges 0-1,1-2,... --size 10 [--suffix 3]
"""
import argparse, sys, time
import numpy as np
from numba import cuda, uint64, int32

MAXW = 32          # max wires (inputs + gates)
MAXK = 8           # max suffix gates
NPAIR_MAX = MAXW * (MAXW - 1) // 2
PL = np.zeros(NPAIR_MAX, np.int32)
PR = np.zeros(NPAIR_MAX, np.int32)
_i = 0
for _r in range(MAXW):
    for _l in range(_r):
        PL[_i], PR[_i] = _l, _r
        _i += 1
ALL = (1 << 256) - 1


def choices(w):
    return w * (w - 1) + w   # AND pairs, OR pairs, NOT singles


def decode(w, c):
    npair = w * (w - 1) // 2
    if c < npair:
        return 0, int(PL[c]), int(PR[c])
    if c < 2 * npair:
        return 1, int(PL[c - npair]), int(PR[c - npair])
    return 2, c - 2 * npair, c - 2 * npair


@cuda.jit(device=True)
def apply(wires, w, c, pl, pr, target, final):
    """Gate c over the first w wires, written to wires[w].
    Returns 2 if it equals the target, 0 if trivial/duplicate (skip), else 1."""
    npair = w * (w - 1) // 2
    if c < npair:
        op = 0; l = pl[c]; r = pr[c]
    elif c < 2 * npair:
        op = 1; l = pl[c - npair]; r = pr[c - npair]
    else:
        op = 2; l = c - 2 * npair; r = l
    hit = True
    for k in range(4):
        a = wires[l, k]
        b = wires[r, k]
        if op == 0:
            v = a & b
        elif op == 1:
            v = a | b
        else:
            v = ~a
        wires[w, k] = v
        if v != target[k]:
            hit = False
    if hit:
        return 2
    if final:
        return 0
    zero = True
    ones = True
    for k in range(4):
        v = wires[w, k]
        if v != uint64(0):
            zero = False
        if v != ~uint64(0):
            ones = False
    if zero or ones:
        return 0
    for i in range(w):
        same = True
        for k in range(4):
            if wires[i, k] != wires[w, k]:
                same = False
                break
        if same:
            return 0
    return 1


@cuda.jit
def suffix_kernel(prefix_tt, nprefix, W, K, target, pl, pr, found, out):
    tid = cuda.grid(1)
    c1count = W * (W - 1) + W
    if tid >= nprefix * c1count or found[0] != 0:
        return
    p = tid // c1count
    c1 = tid % c1count
    wires = cuda.local.array((MAXW, 4), uint64)
    choice = cuda.local.array(MAXK, int32)
    for i in range(W):
        for k in range(4):
            wires[i, k] = prefix_tt[p, i, k]
    choice[0] = c1
    s = apply(wires, W, c1, pl, pr, target, K == 1)
    hit_depth = -1
    if s == 2:
        hit_depth = 0
    elif s == 1 and K >= 2:
        if K == 2:
            w = W + 1
            for c in range(w * (w - 1) + w):
                if apply(wires, w, c, pl, pr, target, True) == 2:
                    choice[1] = c
                    hit_depth = 1
                    break
        else:
            d = 1
            choice[1] = -1
            while d >= 1 and hit_depth < 0:
                if found[0] != 0:
                    return
                w = W + d
                choice[d] += 1
                if choice[d] >= w * (w - 1) + w:
                    d -= 1
                    continue
                s = apply(wires, w, choice[d], pl, pr, target, False)
                if s == 2:
                    hit_depth = d
                    break
                if s == 0:
                    continue
                if d + 1 == K - 1:
                    w2 = w + 1
                    for c in range(w2 * (w2 - 1) + w2):
                        if apply(wires, w2, c, pl, pr, target, True) == 2:
                            choice[d + 1] = c
                            hit_depth = d + 1
                            break
                    continue
                d += 1
                choice[d] = -1
    if hit_depth >= 0:
        if cuda.atomic.cas(found, 0, 0, 1) == 0:
            out[0] = p
            out[1] = hit_depth + 1
            for i in range(hit_depth + 1):
                out[2 + i] = choice[i]


def to_words(tt):
    return [(tt >> (64 * k)) & (2**64 - 1) for k in range(4)]


def gate_tt(op, a, b):
    return a & b if op == 0 else a | b if op == 1 else ALL ^ a


def derive(inputs, fset):
    """Greedy one-gate-at-a-time derivation of a set of functions from the inputs."""
    wires, gates, rest = list(inputs), [], set(fset)
    while rest:
        for f in sorted(rest):
            g = next(((op, l, r) for r in range(len(wires)) for l in range(r + 1)
                      for op in (0, 1, 2)
                      if (op == 2) == (l == r) and gate_tt(op, wires[l], wires[r]) == f), None)
            if g:
                gates.append(g); wires.append(f); rest.discard(f)
                break
        else:
            raise RuntimeError('set not derivable')
    return wires, gates


def lean_eval(n, gates, out_wire, xbits):
    """Mirror of PEqualNP.CircuitLowerBounds.Circuit.eval for fan-in-2 AND/OR/NOT gates."""
    w = list(xbits)
    for op, l, r in gates:
        ins = [w[l]] if op == 2 else [w[l], w[r]]
        w.append(all(ins) if op == 0 else any(ins) if op == 1 else not ins[0])
    return w[out_wire] if out_wire < len(w) else False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--edges', required=True, help='e.g. 0-1,1-2,0-7')
    ap.add_argument('--size', type=int, required=True)
    ap.add_argument('--suffix', type=int, default=3)
    ap.add_argument('--batch', type=int, default=1 << 16, help='prefixes per GPU launch')
    a = ap.parse_args()
    n = a.n
    edges = [tuple(map(int, e.split('-'))) for e in a.edges.split(',')]
    inputs = [sum(1 << x for x in range(256) if x >> i & 1) for i in range(n)]
    target = sum(1 << x for x in range(256) if any(x >> u & 1 and x >> v & 1 for u, v in edges))
    K = min(a.suffix, a.size)
    P = a.size - K
    t0 = time.time()

    witness = None
    level = {frozenset()}
    for depth in range(P):
        nxt = set()
        for S in level:
            wires = inputs + sorted(S)
            known = set(wires)
            w = len(wires)
            for c in range(choices(w)):
                op, l, r = decode(w, c)
                f = gate_tt(op, wires[l], wires[r])
                if f == target:
                    witness = (S, [(op, l, r)])
                    break
                if f in (0, ALL) or f in known:
                    continue
                nxt.add(S | {f})
            if witness:
                break
        if witness:
            break
        level = nxt
        print(f'prefix level {depth + 1}: {len(level)} sets ({time.time() - t0:.1f}s)', flush=True)

    if not witness and K > 0:
        W = n + P
        assert W + K <= MAXW and K <= MAXK
        tgt = cuda.to_device(np.array(to_words(target), np.uint64))
        dpl, dpr = cuda.to_device(PL), cuda.to_device(PR)
        found = cuda.to_device(np.zeros(1, np.int32))
        out = cuda.to_device(np.zeros(2 + MAXK, np.int32))
        sets = list(level)
        c1 = choices(W)
        print(f'GPU: {len(sets)} prefixes x {K} suffix gates ({c1} first-gate choices)', flush=True)
        for b in range(0, len(sets), a.batch):
            chunk = sets[b:b + a.batch]
            arr = np.array([[to_words(t) for t in inputs + sorted(S)] for S in chunk], np.uint64)
            nthreads = len(chunk) * c1
            tpb = 128
            suffix_kernel[(nthreads + tpb - 1) // tpb, tpb](
                cuda.to_device(arr), len(chunk), W, K, tgt, dpl, dpr, found, out)
            cuda.synchronize()
            if found.copy_to_host()[0]:
                o = out.copy_to_host()
                S = chunk[o[0]]
                wires = inputs + sorted(S)
                suf = []
                for i in range(o[1]):
                    op, l, r = decode(len(wires), int(o[2 + i]))
                    suf.append((op, l, r))
                    wires.append(gate_tt(op, wires[l], wires[r]))
                witness = (S, suf)
                break
            done = min(b + a.batch, len(sets))
            print(f'  {done}/{len(sets)} prefixes, none ({time.time() - t0:.1f}s)', flush=True)

    if witness:
        S, suf = witness
        wires, gates = derive(inputs, S)
        # suffix indices referred to inputs + sorted(S); remap to the derived order
        pos = {f: i for i, f in enumerate(wires)}
        order = inputs + sorted(S)
        for op, l, r in suf:
            gl, gr = order[l], order[r]
            f = gate_tt(op, gl, gr)
            gates.append((op, pos[gl], pos[gr]))
            order.append(f)
            wires.append(f)
            pos[f] = len(wires) - 1
        out_wire = len(wires) - 1
        ok = all(lean_eval(n, gates, out_wire, [bool(x >> i & 1) for i in range(n)])
                 == any(x >> u & 1 and x >> v & 1 for u, v in edges) for x in range(1 << n))
        names = ['AND', 'OR', 'NOT']
        print(f'WITNESS with {len(gates)} gates, verified={ok} ({time.time() - t0:.1f}s)')
        for j, (op, l, r) in enumerate(gates):
            print(f'  w{n + j} = {names[op]}(w{l}' + (')' if op == 2 else f', w{r})'))
        sys.exit(0 if ok else 2)
    print(f'NONE: no circuit with <= {a.size} gates ({time.time() - t0:.1f}s)')


if __name__ == '__main__':
    main()
