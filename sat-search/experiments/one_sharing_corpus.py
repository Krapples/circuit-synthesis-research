"""One-sharing exact fast path (theory/one_sharing_core.py) after module preprocessing, on the frozen corpus.

For each complete target (essential restriction):
  monotone basis (monotone targets): raw simplification -> core; solve_core(core, signed=False) decides
      excess <= 1 exactly; if yes, the monotone minimum is n_core - 1 + excess + len(trace) (raw contraction
      preserves monotone and counted cost);
  free-NOT binary: signed simplification -> core; solve_core(core, signed=True) likewise for binary gates
      with free NOTs (signed contraction is exact for free-NOT binary cost only);
  counted NOT (signed-irreducible originals only): certified_total(n, f) gives the exact unrestricted total
      when the NOT count at the one-sharing budget is <= Markov inversion + 1;
  star_candidates: construction upper bounds (binary gates n + k - 2) for single-primary sharing patterns;
      a failed recognition is NOT an exclusion.
Compared with the recorded intervals (results/signed_bound_compare.jsonl for NOT-enabled; ablation/endpoint
records for monotone). Writes results/one_sharing_corpus.jsonl. Usage: python experiments/one_sharing_corpus.py"""
import ast, json, os, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
from module_contraction import simplify, raw_monotone, contract_pair, peel, essential
from one_sharing_core import solve_core, certified_total, star_candidates, ev
from signed_bound_compare import cases, restrict_essential


def mono_intervals():
    out = {}
    for path in ('results/synthesis_ablation.jsonl', 'results/synthesis_endpoints.jsonl'):
        for line in open(os.path.join(HERE, path), encoding='utf-8'):
            r = json.loads(line)
            if r.get('kind') == 'interval' and r.get('basis') == 'mono':
                fin = r['final'] if isinstance(r['final'], dict) else ast.literal_eval(r['final'])
                lo, hi = out.get(r['case'], (0, 10 ** 9))
                out[r['case']] = (max(lo, fin['lower']), min(hi, fin['upper']))
    return out


if __name__ == '__main__':
    notiv = {json.loads(l)['case']: json.loads(l) for l in open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'))}
    moniv = mono_intervals()
    out = open(os.path.join(HERE, 'results', 'one_sharing_corpus.jsonl'), 'w', encoding='utf-8')
    tally = dict(cases=0, mono_exact=0, mono_new=0, free_exact=0, counted_exact=0, counted_new=0, star_upper_new=0)
    for name, fam, n0, f0 in cases():
        n, f, _ = restrict_essential(n0, f0)
        if n < 2:
            continue
        rec = dict(case=name, family=fam, n=n)
        t0 = time.time()
        if raw_monotone(n, f):
            m, core, tr = simplify(n, f, False)
            ans = solve_core(m, core, False, False)
            if ans is not None:
                rec['mono_exact'] = ans[0] + len(tr)
        m, core, tr = simplify(n, f, True)
        ans = solve_core(m, core, True, False)
        if ans is not None:
            rec['free_binary_exact'] = ans[0] + len(tr)
        if contract_pair(n, f, True) is None and peel(n, f, True) is None:
            z = certified_total(n, f)
            if z is not None:
                rec['counted_exact'] = z[0]
        stars = [b for b, t in star_candidates(n, f, False)] if raw_monotone(n, f) else []
        if stars:
            rec['star_upper_binary'] = min(stars)
        rec['seconds'] = round(time.time() - t0, 3)
        p = notiv.get(name, {}); lo_not = max(p.get('support', 0), p.get('existing') or 0, p.get('sat_lower') or 0, p.get('signed') or 0) if p else None
        hi_not = p.get('upper'); hi_not = None if hi_not in (None, 10 ** 9) else hi_not
        lo_m, hi_m = moniv.get(name, (None, None))
        rec.update(not_interval=[lo_not, hi_not], mono_interval=[lo_m, hi_m])
        tally['cases'] += 1
        if 'mono_exact' in rec:
            tally['mono_exact'] += 1
            if lo_m is not None and lo_m < hi_m:
                tally['mono_new'] += 1
            if hi_m not in (None, 10 ** 9) and rec['mono_exact'] > hi_m:
                print(f'!!! {name}: mono exact {rec["mono_exact"]} > recorded upper {hi_m}', flush=True)
        tally['free_exact'] += 'free_binary_exact' in rec
        if 'counted_exact' in rec:
            tally['counted_exact'] += 1
            if lo_not is not None and (hi_not is None or lo_not < hi_not):
                tally['counted_new'] += 1
            if hi_not is not None and rec['counted_exact'] > hi_not:
                print(f'!!! {name}: counted exact {rec["counted_exact"]} > recorded upper {hi_not}', flush=True)
        if 'star_upper_binary' in rec and hi_m not in (None, 10 ** 9) and rec['star_upper_binary'] < hi_m:
            tally['star_upper_new'] += 1
        out.write(json.dumps(rec) + '\n')
        flags = [k for k in ('mono_exact', 'free_binary_exact', 'counted_exact', 'star_upper_binary') if k in rec]
        if flags:
            print(f'{name:22} n={n} ' + ' '.join(f'{k}={rec[k]}' for k in flags) +
                  f' NOT={rec["not_interval"]} mono={rec["mono_interval"]} {rec["seconds"]}s', flush=True)
    print('SUMMARY', tally)
