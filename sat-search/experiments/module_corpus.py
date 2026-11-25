"""Exact module preprocessing and the typed sharing+NOT bound on the frozen corpus.

For every complete target (results/synthesis_cases.json, results/synthesis_signed_cases.json), restricted to
its essential inputs:
  * raw simplification (AND/OR module contraction + canalizing peels, theory/module_contraction.simplify):
    min_counted(f) = len(trace) + min_counted(core) and the same for monotone AND/OR cost;
  * total-gate lower bounds: signed (n-1 + lower + not_lower), typed (n-1 + typed_lower, joint sharing and
    NOT), and typed on the reduced core plus the trace length;
  * comparison with the best prior NOT-basis lower bound and verified upper bound from
    results/signed_bound_compare.jsonl.
Writes results/module_corpus.jsonl. Usage: python experiments/module_corpus.py"""
import json, os, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'theory')); sys.path.insert(0, os.path.join(HERE, 'experiments'))
from signed_bound_compare import cases, restrict_essential
from module_contraction import simplify
from signed_typed_bound import TypedBound


def typed_total(n, f):
    if n < 2:
        return max(0, n - 1)
    b = TypedBound(n, f)
    return n - 1 + b.typed_lower()


if __name__ == '__main__':
    prior = {}
    for line in open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'), encoding='utf-8'):
        r = json.loads(line)
        prior[r['case']] = r
    out = open(os.path.join(HERE, 'results', 'module_corpus.jsonl'), 'w', encoding='utf-8')
    agg = dict(cases=0, reducible=0, inputs_removed=0, fully_reduced=0, typed_gain_over_signed=0,
               core_gain_over_typed=0, new_over_prior=0, resolved=0)
    for name, fam, n0, f0 in cases():
        n, f, _ = restrict_essential(n0, f0)
        if n < 2 or f in (0, (1 << (1 << n)) - 1):
            continue
        t0 = time.time()
        m, core, trace = simplify(n, f, signed=False)
        t_red = time.time() - t0
        t1 = time.time()
        typed = typed_total(n, f)
        t_typed = time.time() - t1
        core_typed = len(trace) + typed_total(m, core)
        p = prior.get(name, {})
        signed = p.get('signed')
        best_prior = max(p.get('support', 0), p.get('existing') or 0, p.get('sat_lower') or 0, signed or 0)
        new = max(typed, core_typed)
        upper = p.get('upper')
        upper = None if upper in (None, 10 ** 9) else upper
        rec = dict(case=name, family=fam, n=n, core_n=m, trace=[list(map(str, s)) for s in trace], signed=signed,
                   typed=typed, core_typed=core_typed, best_prior=best_prior, upper=upper,
                   seconds_reduce=round(t_red, 4), seconds_typed=round(t_typed, 3))
        out.write(json.dumps(rec) + '\n')
        agg['cases'] += 1
        agg['reducible'] += bool(trace)
        agg['inputs_removed'] += len(trace)
        agg['fully_reduced'] += m == 1
        agg['typed_gain_over_signed'] += signed is not None and typed > signed
        agg['core_gain_over_typed'] += core_typed > typed
        agg['new_over_prior'] += new > best_prior
        agg['resolved'] += upper is not None and best_prior < upper <= new
        if upper is not None and new > upper:
            print(f'!!! UNSOUND {name}: bound {new} > verified upper {upper}', flush=True)
        flag = ' NEW' if new > best_prior else ''
        print(f'{name:22} n={n} core={m} (-{len(trace)}) signed={signed} typed={typed} core+trace={core_typed} '
              f'prior={best_prior} upper={upper}{flag} [{t_red:.3f}s reduce, {t_typed:.2f}s typed]', flush=True)
    print('SUMMARY', agg)
