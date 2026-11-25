"""Exact NOT minimization on signed skeletons (theory/skeleton_not_opt.py) as a construction postprocessor.

Part A: every recorded counted-NOT witness in results/*.jsonl (synthesis sweeps) is converted to a signed
AND/OR skeleton (NOT chains folded into edge phases, output cone trimmed), its NOT gates are optimized
globally (polynomial min-cut when the signed dependency graph is balanced, else the three-state shared-wire
DP), the circuit is rebuilt and checked on every row, and the total gate count is compared with the original
and with the recorded NOT-basis upper endpoint.
Part B: competitiveness of "signed skeleton of minimum free-NOT binary size + exact NOT optimization" with the
true counted minimum (reference), for every 3-input function with all inputs essential. Skeletons use AND
gates with input/output phases (complete with free NOTs).
Writes results/skeleton_not_bench.jsonl. Usage: python experiments/skeleton_not_bench.py"""
import ast, glob, json, os, sys, time
from collections import Counter
from itertools import combinations, product
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'verify'):
    sys.path.insert(0, os.path.join(HERE, d))
import reference as ref
from skeleton_not_opt import optimize, balanced_optimize, materialize, structure
from module_contraction import brute


def to_skeleton(n, gates, output):
    """Counted circuit (op 0 AND, 1 OR, 2 NOT) -> (m, signed gates, out phase, used inputs) or None."""
    def resolve(w):
        k = 0
        while w >= n and gates[w - n][0] == 2:
            w = gates[w - n][1]; k ^= 1
        return w, k
    root, out = resolve(output)
    if root < n:
        return None                              # literal output: no binary skeleton
    live, stack = set(), [root]
    while stack:
        w = stack.pop()
        if w in live:
            continue
        live.add(w)
        if w >= n:
            op, l, r = gates[w - n]
            for u in ((l,) if op == 2 else (l, r)):
                stack.append(resolve(u)[0])
    inputs = sorted(w for w in live if w < n)
    binary = sorted(w for w in live if w >= n)
    ids = {w: i for i, w in enumerate(inputs)}
    ids.update({w: len(inputs) + i for i, w in enumerate(binary)})
    sk = []
    for w in binary:
        op, l, r = gates[w - n]
        (ul, pl), (ur, pr) = resolve(l), resolve(r)
        if ul == ur:
            return None                          # degenerate gate (x op x or x op NOT x)
        a, b = (ids[ul], pl), (ids[ur], pr)
        if a[0] > b[0]:
            a, b = b, a
        sk.append(('AND' if op == 0 else 'OR', a[0], b[0], a[1], b[1]))
    return len(inputs), sk, out, inputs


def opt_skeleton(m, sk, out):
    res = balanced_optimize(m, sk, out)
    mode = 'mincut'
    if res is None:
        shared = sum(1 for x in structure(m, sk, out) if len(x) > 1)
        if shared > 14:
            return None, 'too-many-shared'
        res = optimize(m, sk, out); mode = 'dp'
    return res, mode


def table_of(m, circ, idx):
    vals = [sum(1 << a for a in range(1 << m) if a >> i & 1) for i in range(m)]
    one = (1 << (1 << m)) - 1
    for g in circ:
        vals.append(one ^ vals[g[1]] if g[0] == 'NOT' else vals[g[1]] & vals[g[2]] if g[0] == 'AND' else vals[g[1]] | vals[g[2]])
    return vals[idx]


def witnesses():
    for path in glob.glob(os.path.join(HERE, 'results', '*.jsonl')):
        for line in open(path, encoding='utf-8'):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            w = r.get('witness')
            if isinstance(w, str):
                try:
                    w = ast.literal_eval(w)
                except Exception:
                    continue
            if isinstance(w, dict) and 'gates' in w and r.get('case'):
                yield os.path.basename(path), r['case'], r.get('basis'), int(r.get('n', 0)), w


if __name__ == '__main__':
    t_all = time.time()
    out = open(os.path.join(HERE, 'results', 'skeleton_not_bench.jsonl'), 'w', encoding='utf-8')
    uppers = {}
    for line in open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'), encoding='utf-8'):
        r = json.loads(line); uppers[r['case']] = (r.get('sat_lower'), r.get('upper'))
    A = Counter(); seen = set()
    for src, case, basis, n, w in witnesses():
        gates = [tuple(g) for g in w['gates']]
        key = (case, tuple(gates), w['output'])
        if key in seen or n < 1:
            continue
        seen.add(key)
        conv = to_skeleton(n, gates, w['output'])
        if conv is None:
            A['skipped_literal_or_degenerate'] += 1; continue
        m, sk, ph, inputs = conv
        t0 = time.time()
        res, mode = opt_skeleton(m, sk, ph)
        if res is None:
            A['skipped_' + mode] += 1; continue
        k, phases = res
        circ, idx = materialize(m, sk, ph, phases)
        # verify: same function as the original circuit restricted to the used inputs
        full = sum(1 << x for x in range(1 << n) if ref.evaluate(n, [g if g[0] != 2 else (2, g[1], g[1]) for g in gates[:w['output'] - n + 1]], x))
        sub = sum(((full >> sum(1 << inputs[i] for i in range(m) if a >> i & 1)) & 1) << a for a in range(1 << m))
        ok = table_of(m, circ, idx) == sub
        before = len([g for g in gates[:w['output'] - n + 1]])
        after = len(circ)
        lo, hi = uppers.get(case, (None, None))
        rec = dict(source=src, case=case, basis=basis, n=n, gates_before=before, binary=len(sk),
                   not_before=sum(1 for g in gates[:w['output'] - n + 1] if g[0] == 2), not_after=k,
                   total_after=after, mode=mode, verified=ok, seconds=round(time.time() - t0, 4), upper=hi)
        out.write(json.dumps(rec) + '\n')
        A['witnesses'] += 1; A['verified'] += ok; A['reduced'] += after < before
        A['upper_improved'] += ok and hi not in (None, 10 ** 9) and after < hi
        if not ok:
            print('!!! verification failed', rec, flush=True)
        if ok and hi not in (None, 10 ** 9) and after < hi:
            print(f'IMPROVED UPPER {case}: {after} < recorded {hi}', flush=True)
    print('Part A', dict(A), flush=True)

    # Part B: n = 3, minimum free-NOT binary skeletons + exact NOT optimization vs counted minimum
    B = Counter(); n = 3; one = (1 << 8) - 1
    free = brute(3, 6, 'free')
    var = [sum(1 << a for a in range(8) if a >> i & 1) for i in range(3)]
    for f in range(1, one):
        if len(ref.essential_inputs(3, f)) != 3:
            continue
        Bstar = free.get(f)
        if Bstar is None or Bstar > 4:
            B['skipped_large'] += 1; continue
        best = None

        def dfs(vals, sk):
            global best
            if len(sk) == Bstar:
                top = vals[-1]
                if top in (f, one ^ f):
                    try:
                        k, _ = optimize(3, sk, int(top != f))
                    except ValueError:
                        return                     # not every node in the output cone
                    best = k if best is None else min(best, k)
                return
            j = len(vals)
            for l, r in combinations(range(j), 2):
                for a, b in product((0, 1), repeat=2):
                    x = vals[l] ^ (one if a else 0); y = vals[r] ^ (one if b else 0)
                    dfs(vals + [x & y], sk + [('AND', l, r, a, b)])
        dfs(list(var), [])
        Mc = ref.minimum(3, f, 'general')[0]
        if best is None:
            B['no_skeleton'] += 1; continue
        two_stage = Bstar + best
        B['functions'] += 1; B['two_stage_optimal'] += two_stage == Mc; B['two_stage_worse'] += two_stage > Mc
        out.write(json.dumps(dict(part='B', f=f, free_binary=Bstar, skeleton_not=best, two_stage=two_stage, counted_min=Mc)) + '\n')
    print('Part B (n=3, B* <= 4)', dict(B), f'{time.time() - t_all:.0f}s', flush=True)
