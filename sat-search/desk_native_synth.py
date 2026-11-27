"""Run desk template units through native/template_synth.exe and write Lean proofs for SAT units.

Statements are parsed by template_synth.parse (rows, budget, basis). Each SAT circuit is re-simulated
here on the statement's rows (Lean semantics) before template_synth.lean_file writes <out>/<id>.lean.
Records go to <out>/native.jsonl (one line per unit: verdict, k, per-k times, the flags used).

  python desk_native_synth.py --gaps gaps.json --templates rect46-andor-search,tl6c-not-search \
      --out results/templates_native [--limit 20] [--ids ...] [--seconds 60] [--threads 11] \
      [--start floor|1] [--native-flags "--no-colex"]

--start floor uses the floor stated in the step's sketch ("a floor of K") as the first size; the
default 1 tries every size, so an UNSAT verdict means no circuit of at most the budget at all.
"""
import argparse, json, os, re, subprocess, sys

from template_synth import parse, simulate, lean_file

EXE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'native', 'template_synth.exe')
OPS = {0: 'and', 1: 'or', 2: 'not'}


def unit_line(gap, spec, start):
    rows = ','.join('%x:%d' % (sum(b << i for i, b in enumerate(bits)), t) for bits, t in spec['rows'])
    return '%s %d %d %d %d %s' % (gap['id'], spec['n'], int(spec['general']), start, spec['size'], rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--gaps', required=True)
    ap.add_argument('--templates', default='')
    ap.add_argument('--ids', default='')
    ap.add_argument('--out', required=True)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--seconds', type=float, default=60)
    ap.add_argument('--threads', type=int, default=11)
    ap.add_argument('--start', default='1')
    ap.add_argument('--native-flags', default='')
    ap.add_argument('--include-held', action='store_true', help='also units with an open PR')
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    gaps = json.load(open(a.gaps, encoding='utf-8'))['gaps']
    want = set(filter(None, a.templates.split(',')))
    ids = set(filter(None, a.ids.split(',')))
    todo = []
    for g in gaps:
        tpl = (g.get('faithful_by_template') or {}).get('template')
        if ids and g['id'] not in ids:
            continue
        if not ids and tpl not in want:
            continue
        if g.get('pr_open') and not a.include_held:
            continue
        spec = parse(g['statement'])
        if spec is None:
            continue
        start = 1
        if a.start == 'floor':
            m = re.search(r'floor of (\d+)', g.get('sketch') or '')
            start = min(int(m.group(1)), spec['size']) if m else 1
        todo.append((g, spec, start))
    if a.limit:
        todo = todo[:a.limit]
    print('units:', len(todo), file=sys.stderr, flush=True)
    by_id = {g['id']: (g, spec, start) for g, spec, start in todo}
    cmd = [EXE, '--threads', str(a.threads), '--seconds', str(a.seconds)] + a.native_flags.split()
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, encoding='utf-8')
    proc.stdin.write(''.join(unit_line(g, s, st) + '\n' for g, s, st in todo))
    proc.stdin.close()
    counts = {}
    seen = set()
    with open(os.path.join(a.out, 'native.jsonl'), 'a', encoding='utf-8') as rec:
        for line in proc.stdout:
            r = json.loads(line)
            seen.add(r['id'])
            g, spec, start = by_id[r['id']]
            r.update(template=(g.get('faithful_by_template') or {}).get('template'), budget=spec['size'],
                     start=start, flags=a.native_flags, cap_s=a.seconds)
            if r['status'] == 'SAT':
                gates = [(OPS[op], [x] if op == 2 else [x, y]) for op, x, y in r['gates']]
                ok = all(simulate(spec['n'], gates, r['out'], bits) == t for bits, t in spec['rows'])
                ok = ok and len(gates) <= spec['size'] and (spec['general'] or all(op != 'not' for op, _ in gates))
                if not ok:
                    r['status'] = 'BAD'
                else:
                    with open(os.path.join(a.out, r['id'] + '.lean'), 'w', encoding='utf-8', newline='\n') as f:
                        f.write(lean_file(dict(g, module='PEqualNP.Outside.' + g['id'].replace('-', '_')),
                                          gates, r['out'], spec['general']))
            counts[r['status']] = counts.get(r['status'], 0) + 1
            rec.write(json.dumps(r) + '\n')
            rec.flush()
            print('%s %s %s k=%s %.1fs' % (r['id'], r['template'], r['status'], r.get('k'), r['seconds']),
                  file=sys.stderr, flush=True)
    rc = proc.wait()
    missing = sorted(set(by_id) - seen)
    print('summary:', counts, 'exit', rc, 'unreported', len(missing), file=sys.stderr)
    if rc or missing:
        sys.exit(1)


if __name__ == '__main__':
    main()
