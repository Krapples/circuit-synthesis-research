"""Native target-directed orientation portfolio: differential replay and benchmark driver.

Runs native/orientation_synth.exe on a batch of targets and evaluates every returned chain row by row here (an
evaluator independent of the C++ code). Modes:

  replay  --input FILE.jsonl --reference REF.jsonl : targets and fallback witnesses from the research bundle input
          (d['witnesses'][-1]), native fallback disabled; compare [orient, reuse] sizes with the Python replay
          sizes (a faithful port should match exactly; any mismatch is reported, not hidden).
  bench   --input FILE.jsonl | --random N:COUNT:SEED : native cofactor witness (n <= 6) or supplied/Shannon fallback,
          then the orientation stages; records sizes and stage times.
"""
import argparse
import json
import random
import subprocess
import sys
from pathlib import Path
from time import perf_counter

HERE = Path(__file__).resolve().parent
EXE = HERE.parent / 'native' / 'orientation_synth.exe'


def spec_of(w):
    return ';'.join(f'{a},{b}' for a, b in w['gates']) + f"|{w['out']}"


def evaluate(n, spec):
    body, out = spec.split('|')
    gates = [tuple(map(int, g.split(','))) for g in body.split(';')] if body else []
    tt = 0
    for row in range(1 << n):
        vals = [0] + [(row >> i) & 1 for i in range(n)]
        for a, b in gates:
            assert a // 2 < len(vals) and b // 2 < len(vals), 'forward reference'
            vals.append((vals[a // 2] ^ (a & 1)) & (vals[b // 2] ^ (b & 1)))
        o = int(out)
        tt |= (vals[o // 2] ^ (o & 1)) << row
    return tt, len(gates)


def run(lines, args, exe=EXE):
    t0 = perf_counter()
    p = subprocess.run([str(exe), *args, '--stdin'], input='\n'.join(lines) + '\n', capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(p.stderr)
    recs = [json.loads(l) for l in p.stdout.splitlines()]
    assert len(recs) == len(lines), (len(recs), len(lines), p.stderr[-500:])
    for line, r in zip(lines, recs):
        n, tt = int(line.split()[0]), int(line.split()[1], 16)
        for key, size in (('spec', r['reuse_size']), ('orient_spec', r['orient_size'])):
            got, k = evaluate(n, r[key])
            assert got == tt and k == size, ('independent evaluation failed', line, key)
    return recs, perf_counter() - t0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('mode', choices=('replay', 'bench'))
    ap.add_argument('out', type=Path)
    ap.add_argument('--input', type=Path, nargs='*', default=[])
    ap.add_argument('--reference', type=Path, nargs='*', default=[])
    ap.add_argument('--random', nargs='*', default=[], help='N:COUNT:SEED random complete targets')
    ap.add_argument('--min-n', type=int, default=0)
    ap.add_argument('--max-n', type=int, default=8)
    ap.add_argument('--with-spec', action='store_true', help='bench: pass the input file witness as fallback too')
    ap.add_argument('--exe-args', default='')
    ap.add_argument('--exe', type=Path, default=EXE)
    a = ap.parse_args()
    cases = []
    for fn in a.input:
        for l in fn.read_text().splitlines():
            d = json.loads(l)
            if a.min_n <= d['n'] <= a.max_n:
                cases.append(dict(n=d['n'], tt=int(d['tt'], 16), name=d.get('name'), family=d.get('family'),
                                  old=d.get('sizes'), spec=spec_of(d['witnesses'][-1]) if 'witnesses' in d else None))
    for item in a.random:
        n, count, seed = map(int, item.split(':'))
        rng = random.Random(seed)
        for i in range(count):
            cases.append(dict(n=n, tt=rng.getrandbits(1 << n), name=f'random-{seed}-{i}', family='random', old=None, spec=None))
    extra = a.exe_args.split()
    if a.mode == 'replay':
        extra = ['--no-native', *extra]
    lines = []
    for c in cases:
        use_spec = c['spec'] and (a.mode == 'replay' or a.with_spec)
        lines.append(f"{c['n']} {c['tt']:x}" + (f" {c['spec']}" if use_spec else ''))
    recs, wall = run(lines, extra, a.exe)
    refs = {}
    for fn in a.reference:
        for l in fn.read_text().splitlines():
            d = json.loads(l)
            refs[(d['n'], int(d['tt'], 16))] = d
    mismatch = 0
    with a.out.open('w') as f:
        for c, r in zip(cases, recs):
            ref = refs.get((c['n'], c['tt']))
            r.update(name=c['name'], family=c['family'], old=c['old'], exe_args=' '.join(extra))
            if ref is not None:
                r['python_sizes'] = ref['sizes']
                r['python_seconds'] = ref.get('seconds')
                if ref['sizes'] != [r['orient_size'], r['reuse_size']]:
                    mismatch += 1
            f.write(json.dumps(r) + '\n')
    summary = {'cases': len(recs), 'wall_seconds': round(wall, 2),
               'fallback': sum(r['fallback_size'] for r in recs), 'orient': sum(r['orient_size'] for r in recs),
               'reuse': sum(r['reuse_size'] for r in recs),
               'native_seconds': round(sum(r['native_seconds'] for r in recs), 3),
               'orient_seconds': round(sum(r['orient_seconds'] for r in recs), 3),
               'strict_improvements': sum(r['reuse_size'] < r['fallback_size'] for r in recs),
               'reference_matched': sum(1 for c in cases if (c['n'], c['tt']) in refs), 'reference_mismatch': mismatch}
    by_n = {}
    for r in recs:
        s = by_n.setdefault(r['n'], [0, 0, 0, 0, 0.0, 0.0])
        s[0] += 1; s[1] += r['fallback_size']; s[2] += r['orient_size']; s[3] += r['reuse_size']
        s[4] += r['native_seconds'] + r['shannon_seconds']; s[5] += r['orient_seconds']
    summary['by_n'] = {n: dict(cases=s[0], fallback=s[1], orient=s[2], reuse=s[3], fallback_seconds=round(s[4], 3),
                               orient_seconds=round(s[5], 3)) for n, s in sorted(by_n.items())}
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    sys.exit(main())
