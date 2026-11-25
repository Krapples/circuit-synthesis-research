"""First-gate elimination bounds versus the strongest production bounds on the frozen corpus.

Complete targets (essential restriction, free-NOT binary gates B; counted total = B + NOT):
  signed_bin  n - 1 + signed regional lower()       (production via --signedregions)
  existing    cube_search general-basis analytical bound (monotone targets)
  fg1         first_gate_bound.lower(mode=1)         (first-gate absorption; affine identification off)
  fg3         first_gate_bound.lower(mode=3)         (recursive combination with the regional bound)
  xor         XOR-factor stripping: 3k + bounds of the core (free-NOT basis only)
  total       max(binary bounds) + not_lower         (valid for the counted-NOT total)
Partial targets: partial_first_gate_bound.bound(first=True) versus first=False (its recursive baseline) and
the recorded production lower endpoints, monotone and free-NOT.
Adaptive invocation: first-gate recursion is skipped above MAXN inputs (timing recorded).
Writes results/first_gate_compare.jsonl. Usage: python experiments/first_gate_compare.py [maxn]"""
import ast, json, os, sys, time
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
from signed_bound_compare import cases, restrict_essential, existing_general
from signed_region_bounds import Bound
from first_gate_bound import lower as fg_lower
from partial_first_gate_bound import bound as partial_bound
from xor_factor import strip_xor


def prior_intervals():
    out = {}
    for line in open(os.path.join(HERE, 'results', 'signed_bound_compare.jsonl'), encoding='utf-8'):
        r = json.loads(line)
        out[r['case']] = r
    return out


def partial_endpoints():
    """Recorded production lower/upper endpoints for partial cases, per basis."""
    out = {}
    for line in open(os.path.join(HERE, 'results', 'synthesis_ablation.jsonl'), encoding='utf-8'):
        r = json.loads(line)
        if r.get('kind') == 'interval':
            fin = r['final'] if isinstance(r['final'], dict) else ast.literal_eval(r['final'])
            key = (r['case'], r['basis'])
            lo, hi = out.get(key, (0, 10 ** 9))
            out[key] = (max(lo, fin['lower']), min(hi, fin['upper']))
    return out


if __name__ == '__main__':
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    pri = prior_intervals()
    out = open(os.path.join(HERE, 'results', 'first_gate_compare.jsonl'), 'w', encoding='utf-8')
    agg = dict(complete=0, fg_over_signed=0, fg_over_production=0, recursive_over_max=0, xor_cases=0,
               xor_gain=0, total_over_prior=0, resolved=0, partial=0, partial_gain_over_baseline=0,
               partial_gain_over_production=0)
    for name, fam, n0, f0 in cases():
        n, f, _ = restrict_essential(n0, f0)
        if n < 2 or f in (0, (1 << (1 << n)) - 1):
            continue
        b = Bound(n, f)
        signed_bin, notl = n - 1 + b.lower(), b.not_lower()
        ex = existing_general(n, f)
        rec = dict(case=name, n=n, signed_bin=signed_bin, existing=ex, not_lower=notl)
        m, core, k = strip_xor(n, f)
        rec['xor_factors'] = k
        t0 = time.time()
        if n <= maxn:
            rec['fg1'] = fg_lower(n, f, 1)
            rec['fg3'] = fg_lower(n, f, 3)
            if k:
                cb = max(m - 1 + Bound(m, core).lower() if m >= 2 else 0, fg_lower(m, core, 1) if m >= 2 else 0)
                rec['xor_bound'] = 3 * k + cb
        rec['seconds_fg'] = round(time.time() - t0, 3)
        prod = max(signed_bin, ex or 0)
        fg = max(rec.get('fg1', 0), rec.get('fg3', 0), rec.get('xor_bound', 0))
        total = max(prod, fg) + notl
        p = pri.get(name, {})
        best_prior = max(p.get('support', 0), p.get('existing') or 0, p.get('sat_lower') or 0, p.get('signed') or 0)
        upper = p.get('upper')
        upper = None if upper in (None, 10 ** 9) else upper
        rec.update(production=prod, first_gate=fg, total=total, best_prior=best_prior, upper=upper)
        if upper is not None and total > upper:
            print(f'!!! UNSOUND {name}: total {total} > verified upper {upper}', flush=True)
        agg['complete'] += 1
        agg['fg_over_signed'] += fg > signed_bin
        agg['fg_over_production'] += fg > prod
        agg['recursive_over_max'] += rec.get('fg3', 0) > max(rec.get('fg1', 0), signed_bin)
        agg['xor_cases'] += k > 0
        agg['xor_gain'] += rec.get('xor_bound', 0) > max(rec.get('fg1', 0), rec.get('fg3', 0), prod)
        agg['total_over_prior'] += total > best_prior
        agg['resolved'] += upper is not None and best_prior < upper <= total
        out.write(json.dumps(rec) + '\n'); out.flush()
        print(f'{name:22} n={n} signed={signed_bin} existing={ex} fg1={rec.get("fg1")} fg3={rec.get("fg3")} '
              f'xor={rec.get("xor_bound")} total={total} prior={best_prior} upper={upper} {rec["seconds_fg"]}s'
              f'{" NEW" if total > best_prior else ""}', flush=True)
    # partial corpus targets
    ends = partial_endpoints()
    for c in json.load(open(os.path.join(HERE, 'results', 'synthesis_cases.json'), encoding='utf-8')):
        n, known, truth = int(c['n']), int(c['known']), int(c['truth'])
        if known == (1 << (1 << n)) - 1:
            continue
        P, N = truth & known, known & ~truth
        for basis, mono in (('mono', True), ('not', False)):
            t0 = time.time()
            base, first = partial_bound(n, P, N, mono, False), partial_bound(n, P, N, mono, True)
            lo, hi = ends.get((c['name'], basis), (None, None))
            rec = dict(case=c['name'], partial=True, basis=basis, n=n, baseline=base, first=first,
                       production_lower=lo, upper=hi, seconds=round(time.time() - t0, 3))
            out.write(json.dumps(rec) + '\n'); out.flush()
            agg['partial'] += 1
            agg['partial_gain_over_baseline'] += first > base
            agg['partial_gain_over_production'] += lo is not None and first > lo
            if hi is not None and hi != 10 ** 9 and first > hi:
                print(f'!!! UNSOUND partial {c["name"]} {basis}: {first} > upper {hi}', flush=True)
            print(f'{c["name"]:22} partial {basis} n={n} baseline={base} first={first} production=[{lo},{hi}] '
                  f'{rec["seconds"]}s', flush=True)
    print('SUMMARY', agg)
