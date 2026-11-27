"""Solve pequalnp.com template synthesis units (upper-bound statements) by SAT and emit Lean proofs.

Handled statement shapes (parsed from gap.statement):
  A  PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin m) => (MASK : N).testBit (m * u.val + v.val)) s
     (also written `fun u v : Fin n`): monotone AND/OR, fan-in <= 2, at most s gates, right on every
     input with exactly one vertex on each side (inputs 0..n-1 the u side, n..n+m-1 the v side).
  B  ∃ C, (FanInTwo|Monotone2) C ∧ C.size ≤ s ∧ ∀ i j : Fin N, C.eval (ofFn k => k = i ∨ k = j)
     = (MASK).testBit (N * min i j + max i j): right on every input with one or two inputs on.
  C  ∃ C, (FanInTwo|Monotone2) C ∧ C.size ≤ s ∧ Represents (fun u v : Fin n => MASK.testBit (m*u+v)) C.

SAT model: exactly s gates (extra gates are harmless padding), each AND/OR of two different earlier
wires or (FanInTwo only) NOT of one earlier wire; output any wire. Every model is re-simulated on all
rows before a Lean file is written. UNSAT means no circuit of at most s gates in this exact model
(fan-in one copies and constants are never needed except for the all-true/all-false tables, which
are handled directly).

Usage:
  python template_synth.py --gaps gaps.json --templates rect46-andor-search,tl6c-not-search \
      --out results/templates --workers 11 [--limit 50] [--ids L-meta-1,L-meta-2]
Writes <out>/<id>.lean for SAT units and appends verdicts to <out>/verdicts.jsonl (resumes: units
already in verdicts.jsonl are skipped).
"""
import argparse, itertools, json, os, re, sys, time
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
sys.path.insert(0, r"C:\Users\Carson\Documents\ChatGPT\P=NP\.scratch-sat")
from multiprocessing import Pool
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

NUM = r'\(?(\d+)(?:\s*:\s*ℕ\))?'


def parse(stmt):
    """Return dict(n_inputs, rows=[(bits tuple, target)], size, general) or None."""
    s = ' '.join(stmt.split())
    m = re.fullmatch(r'PEqualNP\.Represents\.RepSizeAtMost \(fun (?:\(u : Fin (\d+)\) \(v : Fin (\d+)\)|u v : Fin (\d+)) => '
                     + NUM + r'\.testBit \((\d+) \* u\.val \+ v\.val\)\) (\d+)', s)
    if m:
        n = int(m.group(1) or m.group(3)); mm = int(m.group(2) or m.group(3))
        mask, mul, size = int(m.group(4)), int(m.group(5)), int(m.group(6))
        if mul != mm:
            return None
        return dict(kind='A', n=n + mm, size=size, general=False, rows=rect_rows(n, mm, mask))
    m = re.fullmatch(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.(FanInTwo|Monotone2) C ∧ '
                     r'C\.size ≤ (\d+) ∧ ∀ i j : Fin (\d+), C\.eval \(List\.ofFn fun k : Fin \3 => decide \(k = i ∨ k = j\)\) = '
                     + NUM + r'\.testBit \((\d+) \* min i\.val j\.val \+ max i\.val j\.val\)', s)
    if m:
        general = m.group(1) == 'FanInTwo'; size = int(m.group(2)); N = int(m.group(3))
        mask, mul = int(m.group(4)), int(m.group(5))
        if mul != N:
            return None
        rows = []
        for i in range(N):
            for j in range(i, N):
                rows.append((tuple(int(k == i or k == j) for k in range(N)), (mask >> (N * i + j)) & 1))
        return dict(kind='B', n=N, size=size, general=general, rows=rows)
    m = re.fullmatch(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.(FanInTwo|Monotone2) C ∧ '
                     r'C\.size ≤ (\d+) ∧ PEqualNP\.Represents\.Represents \(fun (?:\(u : Fin (\d+)\) \(v : Fin (\d+)\)|u v : Fin (\d+)) => '
                     + NUM + r'\.testBit \((\d+) \* u\.val \+ v\.val\)\) C', s)
    if m:
        general = m.group(1) == 'FanInTwo'; size = int(m.group(2))
        n = int(m.group(3) or m.group(5)); mm = int(m.group(4) or m.group(5))
        mask, mul = int(m.group(6)), int(m.group(7))
        if mul != mm:
            return None
        return dict(kind='C', n=n + mm, size=size, general=general, rows=rect_rows(n, mm, mask))
    return None


def rect_rows(n, m, mask):
    rows = []
    for u in range(n):
        for v in range(m):
            bits = tuple(int(k == u) for k in range(n)) + tuple(int(k == v) for k in range(m))
            rows.append((bits, (mask >> (m * u + v)) & 1))
    return rows


def simulate(n, gates, out, bits):
    w = list(bits)
    for op, ins in gates:
        vals = [w[i] if i < len(w) else 0 for i in ins]
        if op == 'and':
            w.append(int(all(vals)))
        elif op == 'or':
            w.append(int(any(vals)))
        else:
            w.append(1 - (vals[0] if vals else 0))
    return w[out] if out < len(w) else 0


def synth(spec, solver_name='maplechrono'):
    n, S, rows, general = spec['n'], spec['size'], spec['rows'], spec['general']
    targets = [t for _, t in rows]
    if not any(targets):
        return [], n + S + 1      # an output wire that never exists reads false
    if all(targets):
        return ([('and', [])], n) if S >= 1 else None
    pool = IDPool(); cl = []
    W = n + S
    val = {(w, r): pool.id(('v', w, r)) for w in range(W) for r in range(len(rows))}
    for w in range(n):
        for r, (bits, _) in enumerate(rows):
            cl.append([val[w, r]] if bits[w] else [-val[w, r]])
    choice = {}
    for g in range(n, W):
        lits = []
        for i, j in itertools.combinations(range(g), 2):
            for op in ('and', 'or'):
                s = pool.id(('s', g, op, i, j)); choice[s] = (g, op, [i, j]); lits.append(s)
                for r in range(len(rows)):
                    v, x, y = val[g, r], val[i, r], val[j, r]
                    if op == 'and':
                        cl += [[-s, -v, x], [-s, -v, y], [-s, v, -x, -y]]
                    else:
                        cl += [[-s, v, -x], [-s, v, -y], [-s, -v, x, y]]
        if general:
            for i in range(g):
                s = pool.id(('n', g, i)); choice[s] = (g, 'not', [i]); lits.append(s)
                for r in range(len(rows)):
                    cl += [[-s, val[g, r], val[i, r]], [-s, -val[g, r], -val[i, r]]]
        cl.append(lits)
        cl += CardEnc.atmost(lits, 1, vpool=pool, encoding=EncType.seqcounter).clauses
    outs = {w: pool.id(('o', w)) for w in range(W)}
    cl.append(list(outs.values()))
    for w in range(W):
        for r, t in enumerate(targets):
            cl.append([-outs[w], val[w, r] if t else -val[w, r]])
    with Solver(name=solver_name, bootstrap_with=cl) as sv:
        if not sv.solve():
            return None
        md = set(l for l in sv.get_model() if l > 0)
    gates = [None] * S
    for s, (g, op, ins) in choice.items():
        if s in md:
            gates[g - n] = (op, ins)
    out = next(w for w in range(W) if outs[w] in md)
    return gates, out


def lean_file(gap, gates, out, basis_general):
    gl = ', '.join('⟨.%s, [%s]⟩' % (op, ', '.join(map(str, ins))) for op, ins in gates)
    k = len(gates)
    lines = ['import PEqualNP.Defs', '']
    lines.append('set_option maxRecDepth 50000 in')
    lines.append('set_option maxHeartbeats 4000000 in')
    lines.append('theorem %s : %s := by' % (gap['module'], gap['statement']))
    lines.append('  refine ⟨⟨[%s], %d⟩, ?_, by decide +kernel, by decide +kernel⟩' % (gl, out))
    lines.append('  intro g hg')
    if k == 0:
        lines.append('  simp at hg')
    else:
        lines.append('  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg')
        lines.append('  rcases hg with %s <;> simp' % ' | '.join(['rfl'] * k))
    return '\n'.join(lines) + '\n'


def job(gap):
    spec = parse(gap['statement'])
    t0 = time.time()
    if spec is None:
        return gap['id'], 'unparsed', None, 0.0
    r = synth(spec)
    dt = time.time() - t0
    if r is None:
        return gap['id'], 'unsat', None, dt
    gates, out = r
    for bits, t in spec['rows']:
        assert simulate(spec['n'], gates, out, bits) == t, gap['id']
    assert len(gates) <= spec['size']
    return gap['id'], 'sat', lean_file(gap, gates, out, spec['general']), dt


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--gaps', required=True)
    ap.add_argument('--templates', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--ids', default='')
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    vpath = os.path.join(a.out, 'verdicts.jsonl')
    done = set()
    if os.path.exists(vpath):
        for l in open(vpath, encoding='utf-8'):
            done.add(json.loads(l)['id'])
    d = json.load(open(a.gaps, encoding='utf-8'))
    want = set(a.templates.split(','))
    ids = set(a.ids.split(',')) if a.ids else None
    todo = [g for g in d['gaps'] if (g.get('faithful_by_template') or {}).get('template') in want
            and not g.get('pr_open') and g['id'] not in done and (ids is None or g['id'] in ids)]
    if a.limit:
        todo = todo[:a.limit]
    print('units to solve:', len(todo), flush=True)
    with Pool(a.workers) as p, open(vpath, 'a', encoding='utf-8') as vf:
        for gid, verdict, text, dt in p.imap_unordered(job, todo):
            tpl = next(g for g in todo if g['id'] == gid)['faithful_by_template']['template']
            if text:
                with open(os.path.join(a.out, gid + '.lean'), 'w', encoding='utf-8', newline='\n') as f:
                    f.write(text)
            vf.write(json.dumps(dict(id=gid, template=tpl, verdict=verdict, seconds=round(dt, 2))) + '\n'); vf.flush()
            print(gid, tpl, verdict, '%.1fs' % dt, flush=True)
