"""Check native/cofactor_synth.exe (C++20 port of the cofactor two-signal construction) independently.

1. The 222 four-input NPN representatives: sizes against the bundle library (results/cofactor_witness/npn4_witnesses.json).
2. All 65,536 four-input functions: native size against the library size of the function's NPN class.
3. Random partial four-, five- and six-input targets (seeded): correctness on the care set only.
4. Frozen corpus cases with 3 <= n <= 6 (complete and partial): native upper bound against verified minima where the
   baseline records have one (an upper bound below a verified minimum would be a bug).
Every chain is re-simulated here row by row (independent of the C++ simulator). No result is used as a lower bound.

Usage: python native_cofactor_check.py OUT.jsonl [--random 2000]
"""
import argparse
import json
import random
import subprocess
import sys
from collections import Counter
from pathlib import Path
from time import perf_counter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
from witness_import import Library  # noqa: E402
from synthesis_cases import corpus  # noqa: E402

EXE = ROOT / 'native/cofactor_synth.exe'


def simulate(n, gates, out):
    tt = 0
    for r in range(1 << n):
        v = [0] + [(r >> i) & 1 for i in range(n)]
        for a, b in gates:
            assert a // 2 < len(v) and b // 2 < len(v) and a >= 2 and b >= 2
            v.append((v[a // 2] ^ (a & 1)) & (v[b // 2] ^ (b & 1)))
        tt |= (v[out // 2] ^ (out & 1)) << r
    return tt


EXE_ARGS = []


def native(jobs):
    """jobs: list of (n, tt, care). Returns parsed records in order, each re-verified here."""
    text = ''.join(f'{n} {tt:x} {care:x}\n' for n, tt, care in jobs)
    p = subprocess.run([str(EXE), *EXE_ARGS, '--stdin'], input=text, capture_output=True, text=True, check=True)
    recs = [json.loads(line) for line in p.stdout.splitlines()]
    assert len(recs) == len(jobs), (len(recs), len(jobs), p.stderr[-500:])
    for (n, tt, care), r in zip(jobs, recs):
        full = (1 << (1 << n)) - 1
        assert (simulate(n, r['gates'], r['output']) ^ tt) & care & full == 0, r
        assert r['size'] == len(r['gates']) <= r['estimate']
    return recs, p.stderr.strip()


def minima():
    best = {}
    for f in ('caps_corpus.jsonl', 'hpercy_corpus.jsonl'):
        for line in (ROOT / 'results/baselines' / f).read_text().splitlines():
            r = json.loads(line)
            if r.get('status') == 'OPTIMAL' and r.get('verified'):
                best[r['name']] = r['size']
    return best


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('out', type=Path)
    p.add_argument('--random', type=int, default=2000)
    p.add_argument('--seed', type=int, default=20261125)
    p.add_argument('--exe-args', default='', help='extra cofactor_synth flags, e.g. "--no-a-first"')
    a = p.parse_args()
    EXE_ARGS[:] = a.exe_args.split()
    lib = Library(ROOT / 'results/cofactor_witness/npn4_witnesses.json')
    size_of = {rep: len(g) for rep, (g, _) in lib.reps.items()}
    out = a.out.open('w')
    summary = {}

    reps = sorted(lib.reps)
    t = perf_counter()
    recs, table = native([(4, f, 0xffff) for f in reps])
    diff = Counter(r['size'] - size_of[f] for f, r in zip(reps, recs))
    summary['npn4_reps'] = {'count': len(reps), 'size_minus_library': dict(diff), 'native_total': sum(r['size'] for r in recs),
                            'library_total': sum(size_of.values()), 'seconds': perf_counter() - t, 'table': table}
    for f, r in zip(reps, recs):
        out.write(json.dumps({'part': 'npn4_reps', 'library_size': size_of[f], **r}) + '\n')

    t = perf_counter()
    recs, _ = native([(4, f, 0xffff) for f in range(1 << 16)])
    diff = Counter(r['size'] - size_of[lib.index[f][0]] for f, r in enumerate(recs))
    summary['all4'] = {'count': 1 << 16, 'size_minus_class_library': dict(diff), 'seconds': perf_counter() - t}

    rng = random.Random(a.seed)
    for n in (4, 5, 6):
        full = (1 << (1 << n)) - 1
        jobs = [(n, rng.getrandbits(1 << n), rng.getrandbits(1 << n) | rng.getrandbits(1 << n)) for _ in range(a.random)]
        jobs += [(n, rng.getrandbits(1 << n), full) for _ in range(a.random)]
        t = perf_counter()
        recs, _ = native(jobs)
        summary[f'random{n}'] = {'count': len(jobs), 'seconds': perf_counter() - t,
                                 'max_size_partial': max(r['size'] for r in recs[:a.random]),
                                 'max_size_complete': max(r['size'] for r in recs[a.random:]),
                                 'mean_size_complete': sum(r['size'] for r in recs[a.random:]) / a.random,
                                 'max_seconds': max(r['seconds'] for r in recs)}

    known = minima()
    cases = [c for c in corpus() if 3 <= c.n <= 6]
    recs, _ = native([(c.n, c.truth, c.known) for c in cases])
    gaps, below = Counter(), []
    for c, r in zip(cases, recs):
        m = known.get(c.name)
        if m is not None:
            gaps[r['size'] - m] += 1
            if r['size'] < m:
                below.append(c.name)
        out.write(json.dumps({'part': 'corpus', 'name': c.name, 'verified_minimum': m,
                              'partial': c.known != (1 << (1 << c.n)) - 1, **r}) + '\n')
    summary['corpus'] = {'count': len(cases), 'with_verified_minimum': sum(gaps.values()),
                         'size_minus_minimum': dict(sorted(gaps.items())), 'below_minimum': below}
    out.write(json.dumps({'summary': summary}) + '\n')
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
