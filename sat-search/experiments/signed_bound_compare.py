"""Signed regional lower bound (theory/signed_region_bounds.py) versus the existing NOT-enabled bounds.

For every complete target of the 100-case corpus (results/synthesis_cases.json) and the 16 nonmonotone
cases (results/synthesis_signed_cases.json): restrict to essential inputs, then compare total-gate lower bounds
  support      n_e - 1;
  existing     cube_search general-basis analytical bounds (recursive bound with closure and colouring,
               polarity formula ports with ordered groups), monotone targets only (they take antichains);
  sat_lower    the NOT-basis lower endpoint established by SAT in the recorded sweeps;
  signed       n_e - 1 + Bound.lower(level, ordered) + Bound.not_lower(), at each level.
A signed bound above sat_lower raises the endpoint; reaching the verified upper endpoint resolves the case.
The signed bound's status is provisional (independently tested, proof from the theory audit, not reviewed
here), so resolutions are conditional on it. Writes results/signed_bound_compare.jsonl.
Usage: python experiments/signed_bound_compare.py"""
import ast, json, os, sys, time, tracemalloc
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'theory'))
import cube_search as cs
from signed_region_bounds import Bound


def restrict_essential(n, f):
    rows = 1 << n
    ess = [i for i in range(n) if any((f >> a & 1) != (f >> (a ^ (1 << i)) & 1) for a in range(rows))]
    g = 0
    for b in range(1 << len(ess)):
        a = sum(1 << ess[k] for k in range(len(ess)) if b >> k & 1)
        g |= (f >> a & 1) << b
    return len(ess), g, ess


def monotone_terms(n, f):
    if any((f >> a & 1) > (f >> (a | 1 << i) & 1) for a in range(1 << n) for i in range(n)):
        return None
    ones = [a for a in range(1 << n) if f >> a & 1]
    return tuple(sorted(a for a in ones if not any(b != a and b & a == b for b in ones)))


def existing_general(n, f):
    T = monotone_terms(n, f)
    if not T:
        return None
    cs.MONO[0], cs.REC_CLOSURE[0], cs.COLOR_BOUNDS[0], cs.ORDERED[0] = False, True, True, True
    T = cs._anti(list(T))
    rec = cs.rec_lb(T, 2)
    port = cs.port_binary_lb(T, cs.port_costs(T, formula=True, polarity=True))
    return max(rec, port)


def sat_intervals():
    out = {}
    for path in ('results/synthesis_ablation.jsonl', 'results/synthesis_endpoints.jsonl'):
        for line in open(os.path.join(HERE, path), encoding='utf-8'):
            r = json.loads(line)
            if r.get('kind') == 'interval' and r.get('basis') == 'not':
                fin = r['final'] if isinstance(r['final'], dict) else ast.literal_eval(r['final'])
                lo, hi = out.get(r['case'], (0, 10 ** 9))
                out[r['case']] = (max(lo, fin['lower']), min(hi, fin['upper']))
    # nonmonotone sweep: lower = largest UNSAT budget + 1, upper = smallest SAT budget
    for line in open(os.path.join(HERE, 'results/synthesis_signed.jsonl'), encoding='utf-8'):
        r = json.loads(line)
        if r.get('kind') != 'job' or r.get('basis') != 'not':
            continue
        lo, hi = out.get(r['case'], (0, 10 ** 9))
        if r['status'] == 'UNSAT':
            lo = max(lo, r['budget'] + 1)
        elif r['status'] in ('SAT', 'WITNESS') or r.get('witness'):
            hi = min(hi, r['budget'])
        out[r['case']] = (lo, hi)
    return out


def cases():
    for path in ('results/synthesis_cases.json', 'results/synthesis_signed_cases.json'):
        for c in json.load(open(os.path.join(HERE, path), encoding='utf-8')):
            n = int(c['n'])
            known, truth = int(c['known']), int(c['truth'])
            if known != (1 << (1 << n)) - 1:
                continue          # partial labels: the signed bound needs a complete function
            yield c['name'], c.get('family', ''), n, truth


if __name__ == '__main__':
    iv = sat_intervals()
    out = open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'), 'w', encoding='utf-8')
    gains = dict(over_support=0, over_existing=0, over_sat_lower=0, resolved=0, cases=0)
    t_all = time.time()
    for name, fam, n, f in cases():
        ne, g, ess = restrict_essential(n, f)
        if ne < 2 or g in (0, (1 << (1 << ne)) - 1):
            continue
        tracemalloc.start()
        t0 = time.time()
        b = Bound(ne, g)
        levels = {}
        for key, (lvl, ordd) in dict(xor=(0, False), pattern=(1, False), sandwich=(2, False), ordered=(2, True)).items():
            t = time.time()
            levels[key] = (b.lower(lvl, ordd), round(time.time() - t, 3))
        nl = b.not_lower()
        peak = tracemalloc.get_traced_memory()[1]
        tracemalloc.stop()
        signed = ne - 1 + levels['ordered'][0] + nl
        ex = existing_general(ne, g)
        lo, hi = iv.get(name, (None, None))
        rec = dict(case=name, family=fam, n=n, essential=ne, support=ne - 1, existing=ex, sat_lower=lo, upper=hi,
                   signed=signed, not_lower=nl, levels=levels, seconds=round(time.time() - t0, 3), peak_bytes=peak)
        out.write(json.dumps(rec) + '\n')
        gains['cases'] += 1
        gains['over_support'] += signed > ne - 1
        gains['over_existing'] += ex is not None and signed > ex
        gains['over_sat_lower'] += lo is not None and signed > lo
        gains['resolved'] += lo is not None and hi is not None and lo < hi and signed >= hi
        flag = ''
        if lo is not None and signed > lo:
            flag = ' RAISES SAT LOWER' + (' -> RESOLVED' if hi is not None and signed >= hi else '')
        print(f'{name:22} n={ne} support={ne - 1} existing={ex} sat=[{lo},{hi}] signed={signed} '
              f'(xor {levels["xor"][0]}, pattern {levels["pattern"][0]}, sandwich {levels["sandwich"][0]}, '
              f'ordered {levels["ordered"][0]}, NOT {nl}) {rec["seconds"]}s{flag}', flush=True)
    print('SUMMARY', gains, f'{time.time() - t_all:.0f}s')
