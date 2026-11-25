"""Exact minima of open corpus cases through module preprocessing.

min(f) = len(trace) + min(core) for raw module contraction and canalizing peels, in the counted-NOT basis
and in the monotone basis (theory/module_contraction.py; independently tested against gate-set enumeration
for n <= 4, proof from the theory audit). For each open reducible case the core is solved exactly by the
independent reference (verify/reference.py) in both bases; a witness for f is rebuilt by lifting the core
witness through the trace and checked on every row, so the upper bound is verified independently of the
theorem. Writes results/module_core_minima.jsonl.
Usage: python experiments/module_core_minima.py"""
import json, os, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'theory'))
sys.path.insert(0, os.path.join(HERE, 'verify')); sys.path.insert(0, os.path.join(HERE, 'experiments'))
import reference as ref
from module_contraction import simplify
from signed_bound_compare import cases, restrict_essential


def lift_circuit(n, gates, step):
    """Circuit for the (n)-input function from a circuit for the (n-1)-input reduced function.
    pair step (i, j, p): the reduced function's last input is the module h(x_i, x_j) (AND for p = 3,
    OR for p = 0); peel step (i, v, c): f = g on x_i = v, constant c otherwise."""
    kind = step[0]
    other_inputs = None
    if kind == 'pair':
        _, i, j, p = step
        other = [k for k in range(n) if k not in (i, j)]
        # wires: inputs 0..n-1, then the module gate at wire n, then the reduced circuit's gates
        module = (0 if p == 3 else 1, min(i, j), max(i, j))
        wire = {l: k for l, k in enumerate(other)}
        wire[n - 2] = n                                   # reduced input n-2 is the module wire
        out = [module]
        base = n - 1                                      # reduced circuit wires n-1.. map to n+1..
        for op, a, b in gates:
            ma = wire[a] if a < n - 1 else a - base + n + 1
            mb = wire[b] if b < n - 1 else b - base + n + 1
            out.append((op, ma, mb) if op == 2 else (op, min(ma, mb), max(ma, mb)))
        return out
    _, i, v, c = step
    other = [k for k in range(n) if k != i]
    wire = {l: k for l, k in enumerate(other)}
    base = n - 1
    out = []
    for op, a, b in gates:
        ma = wire[a] if a < n - 1 else a - base + n
        mb = wire[b] if b < n - 1 else b - base + n
        out.append((op, ma, mb) if op == 2 else (op, min(ma, mb), max(ma, mb)))
    g = n + len(out) - 1 if out else wire[0] if n - 1 == 1 else None
    # f = (x_i == v) ? g : c  ->  v=1,c=0: AND(x_i, g); v=0,c=1: OR(x_i, g); other cases need a NOT
    lit = i
    if (v, c) in ((1, 0), (0, 1)):
        out.append((0 if (v, c) == (1, 0) else 1, min(lit, g), max(lit, g)))
    else:
        out.append((2, lit, lit))
        nl = n + len(out) - 1
        out.append((0 if (v, c) == (0, 0) else 1, min(nl, g), max(nl, g)))
    return out


def solve_case(item):
    name, n0, f0 = item
    if True:
        n, f, _ = restrict_essential(n0, f0)
        m, core, trace = simplify(n, f, signed=False)
        rec = dict(case=name, n=n, core_n=m, trace=[list(map(str, s)) for s in trace])
        for basis in ('general', 'monotone'):
            mono_core = all((core >> a & 1) <= (core >> (a | 1 << i) & 1) for a in range(1 << m) for i in range(m))
            if basis == 'monotone' and not mono_core:
                continue
            t0 = time.time()
            Mc, wc = ref.minimum(m, core, basis, seconds=300) if m >= 1 else (0, [])
            rec[f'{basis}_core_min'] = Mc
            rec[f'{basis}_seconds'] = round(time.time() - t0, 2)
            if Mc in (None, 'undecided'):
                continue
            rec[f'{basis}_min'] = len(trace) + Mc
            # rebuild and check a witness for f
            gates, k = [tuple(g) for g in wc], m
            ok = True
            try:
                for step in reversed(trace):
                    gates = lift_circuit(k + 1, gates, tuple(step) if not isinstance(step, tuple) else step)
                    k += 1
                ok = len(gates) == len(trace) + Mc and all(ref.evaluate(n, gates, x) == (f >> x & 1) for x in range(1 << n))
            except Exception as e:
                ok = f'lift failed: {e!r}'
            rec[f'{basis}_witness_verified'] = ok
    return rec


if __name__ == '__main__':
    from multiprocessing import Pool
    targets = sys.argv[1:] or ['hypergraph-18', 'hypergraph-24', 'random-monotone-03', 'random-monotone-04',
                               'random-monotone-08', 'random-monotone-10', 'generated-08', 'generated-09',
                               'comparator-04', 'comparator-07', 'comparator-10']
    path = os.path.join(HERE, 'results', 'module_core_minima.jsonl')
    done = {json.loads(l)['case'] for l in open(path, encoding='utf-8')} if os.path.exists(path) else set()
    items = [(name, n0, f0) for name, fam, n0, f0 in cases() if name in targets and name not in done]
    print(f'{len(items)} cases to solve in parallel, {len(done)} already recorded', flush=True)
    out = open(path, 'a', encoding='utf-8')            # append: never overwrite recorded cases
    with Pool(max(1, min(11, len(items)))) as p:
        for rec in p.imap_unordered(solve_case, items):
            out.write(json.dumps(rec) + '\n'); out.flush()
            print(json.dumps(rec), flush=True)
