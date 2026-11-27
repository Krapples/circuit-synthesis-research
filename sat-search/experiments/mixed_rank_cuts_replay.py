"""Pruning coverage of mixed-rank cuts on captured Percy CEGAR models (logs/restriction_capture).

Each captured model is a full candidate AIG chain at budget k ([op, a, b], inputs 0..n-1, step j is wire n+j,
output the last step). A cut (floor, rank, side) from mixed_rank_cuts.select_cuts excludes the model when fewer
than `floor` steps of the output cone read both sides. Counting is done here by direct structural propagation,
independently of the native CNF (percy_run --mixed-rank-cuts). Arms: floor >= 1 and floor >= 2 cuts (at most 8).

Usage: python -B experiments/mixed_rank_cuts_replay.py logs/restriction_capture [--output PATH]
"""
import argparse, json, os, sys
from collections import Counter
from pathlib import Path
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.append(os.path.join(os.path.dirname(os.path.dirname(HERE)), '.scratch-sat'))
from mixed_rank_cuts import select_cuts, structural_mixed_counts  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('capture', type=Path)
    ap.add_argument('--n', type=int, default=4)
    ap.add_argument('--output', type=Path)
    a = ap.parse_args()
    totals, rows = Counter(), []
    for path in sorted(a.capture.glob('*.models.jsonl')):
        mode, target, k = path.name.split('.')[0].split('_')
        tt = int(target, 16)
        arms = {f'floor{m}': select_cuts(a.n, tt, 8, m) for m in (1, 2)}
        stats = Counter()
        for line in path.read_text().splitlines():
            chain = json.loads(line)['chain']
            gates = [(0, x, y) for _, x, y in chain]  # every Percy AIG step is an AND type: op 0 (not NOT)
            out = a.n + len(gates) - 1
            stats['models'] += 1
            for arm, cuts in arms.items():
                if any(structural_mixed_counts(a.n, gates, out, side) < floor for floor, _, side in cuts):
                    stats[f'{arm}_excluded'] += 1
        rec = dict(mode=mode, target=target, k=int(k), cuts={arm: [list(c) for c in cuts] for arm, cuts in arms.items()},
                   **stats)
        rows.append(rec)
        totals.update(stats)
        print(json.dumps(rec), flush=True)
    print(json.dumps(dict(totals=dict(totals))))
    if a.output:
        a.output.write_text(''.join(json.dumps(r) + '\n' for r in rows) + json.dumps(dict(totals=dict(totals))) + '\n')


if __name__ == '__main__':
    main()
