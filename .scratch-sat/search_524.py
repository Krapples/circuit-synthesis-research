import sys
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc

edges = [3, 6, 12, 24, 48, 96, 65, 129]
def target(x):
    return any(x & edge == edge for edge in edges)

num_gates = int(sys.argv[1])
output = 7 + num_gates
pool = IDPool()
clauses = []
ops = {j: [pool.id((j, op)) for op in ('and', 'or', 'not')] for j in range(8, output + 1)}
select = {(j, k): [pool.id((j, k, i)) for i in range(j)] for j in ops for k in range(2)}

def one(options):
    clauses.extend(CardEnc.equals(options, 1, vpool=pool).clauses)

for j, (a, o, n) in ops.items():
    left, right = select[j, 0], select[j, 1]
    one([a, o, n])
    one(left)
    one(right)
    for i in range(j):
        clauses += [[-left[i], -right[l]] for l in range(i)]
        clauses += [[-left[i], -right[i], n], [-n, -left[i], right[i]]]
        if i >= 8:
            clauses.append([-n, -left[i], -ops[i][2]])
    if j == output:
        continue
    next_left, next_right = select[j + 1, 0], select[j + 1, 1]
    for i in range(j):
        for l in range(i):
            clauses.append([-right[i], -next_right[l]])
        for l in range(i):
            for k in range(l):
                clauses.append([-right[i], -next_right[i], -left[l], -next_left[k]])

for i in range(output):
    clauses.append([select[j, k][i] for j in range(max(8, i + 1), output + 1) for k in range(2)])

def evaluate(circuit, x):
    values = [bool(x >> i & 1) for i in range(8)]
    for op, l, r in circuit:
        match op:
            case 0: values.append(values[l] and values[r])
            case 1: values.append(values[l] or values[r])
            case 2: values.append(not values[l])
    return values[-1]

def row(x):
    val = [pool.id(('val', x, j)) for j in range(output + 1)]
    yield from ([val[i] if x >> i & 1 else -val[i]] for i in range(8))
    for j, (a, o, n) in ops.items():
        l, r = [pool.id(('arg', x, j, k)) for k in range(2)]
        for k, arg in enumerate((l, r)):
            for i, sel in enumerate(select[j, k]):
                yield [-sel, -arg, val[i]]
                yield [-sel, arg, -val[i]]
        f = val[j]
        yield from ([-a,-l,-r,f],[-a,l,-f],[-a,r,-f],
                    [-o,l,r,-f],[-o,-l,f],[-o,-r,f],
                    [-n,-l,-f],[-n,l,f])
    yield [val[-1] if target(x) else -val[-1]]

with Solver(name=sys.argv[2], bootstrap_with=clauses) as solver:
    rows = {0, 255, *edges, *(1 << i for i in range(8))}
    rows |= {x for x in range(256) if not target(x)
             and all(target(x | (1 << i)) for i in range(8) if not x >> i & 1)}
    for x in sorted(rows):
        solver.append_formula(list(row(x)))
    rounds = 0
    print('Searching', num_gates, 'gates with',len(rows),'starting rows', flush=True)
    while solver.solve():
        model = set(solver.get_model())
        circuit = [(next(k for k, v in enumerate(ops[j]) if v in model),
                    *(next(i for i,v in enumerate(select[j,k]) if v in model) for k in range(2))) for j in ops]
        bad = [x for x in range(256) if evaluate(circuit, x) != target(x)]
        if not bad:
            print('WITNESS', circuit, flush=True)
            break
        assert not rows.intersection(bad)
        rounds += 1
        print('Round',rounds,'failed on',len(bad),'rows with',solver.accum_stats(),flush=True)
        for x in bad:
            solver.append_formula(list(row(x)))
        rows.update(bad)
    else:
        print('UNSAT', rounds, solver.accum_stats(), flush=True)
