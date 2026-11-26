"""Differential check of native/fq_check.exe (src/feature_quotient.hpp) against a research support table.

Input: JSONL records with rows, edges, m, pair, support (the minimum support s*, null when none exists) as written by
quotient_completion_research/quotient.py. For every record the native s*, pair-cover size and status must match, every
learned walk must replay natively, and the native conditional bound max(0, s* - 1) is recorded. Records with an
empty edge set must be reported constant; records without a support impossible.
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

EXE = Path(__file__).resolve().parent.parent / 'native' / 'fq_check.exe'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path)
    ap.add_argument('out', type=Path)
    a = ap.parse_args()
    recs = [json.loads(l) for l in a.input.read_text().splitlines() if l.strip()]
    lines = [' '.join(map(str, [d['m'], len(d['rows']), *d['rows'], len(d['edges']), *[x for e in d['edges'] for x in e]]))
             for d in recs]
    p = subprocess.run([str(EXE), '--stdin'], input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True)
    got = [json.loads(l) for l in p.stdout.splitlines()]
    assert len(got) == len(recs)
    bad, stats = [], {}
    with a.out.open('w') as f:
        for d, g in zip(recs, got):
            want = 'constant' if not d['edges'] else 'impossible' if d.get('support') is None else 'feasible'
            ok = g['status'] == want and g['replay']
            if want == 'feasible':
                ok = ok and g['s'] == d['support'] and g['pair_s'] == d['pair']
            if not ok:
                bad.append((d.get('family'), d.get('name'), g))
            stats[want] = stats.get(want, 0) + 1
            f.write(json.dumps({'family': d.get('family'), 'name': d.get('name'), 'research_support': d.get('support'),
                                'research_pair': d.get('pair'), **g}) + '\n')
    feas = [g for g in got if g['status'] == 'feasible']
    print(json.dumps({'records': len(recs), 'by_status': stats, 'mismatches': len(bad),
                      'parity_above_pair': sum(g['s'] > g['pair_s'] for g in feas),
                      'learned_walks': sum(g['learned'] for g in got), 'first_mismatches': bad[:5]}, indent=1))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
