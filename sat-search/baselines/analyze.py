"""Summarize run_baselines.py JSONL records.

Per tool: solved (optimal) count, wrong/unverified count, PAR-2 (unsolved = 2 x deadline), total and median time on
the instances every compared tool solved (matched), summed time on SAT budgets and on UNSAT budgets (from per-budget
records), peak memory. Breakdowns by input count n and by optimum size class. Size disagreements between tools on
the same target are reported (they would indicate a bug or a basis mismatch). Writes cactus data (sorted solve times)
next to the input as <stem>_cactus.json.
usage: python analyze.py <records.jsonl> [--tools t1,t2] [--by n|size|family]"""
import json, os, statistics, sys
from collections import defaultdict


def load(p):
    return [json.loads(l) for l in open(p, encoding='utf-8')]


def main():
    path = sys.argv[1]; opt = dict(zip(sys.argv[2::2], sys.argv[3::2]))
    R = [r for r in load(path) if r['tool'] != '*']
    tools = opt['--tools'].split(',') if '--tools' in opt else sorted({r['tool'] for r in R})
    R = [r for r in R if r['tool'] in tools]
    by = defaultdict(dict)
    for r in R:
        by[r['name']][r['tool']] = r
    # agreement on optimum size
    conflicts = [(nm, {t: x['size'] for t, x in d.items() if x['status'] == 'OPTIMAL'}) for nm, d in by.items()
                 if len({x['size'] for x in d.values() if x['status'] == 'OPTIMAL'}) > 1]
    size_of = {nm: next((x['size'] for x in d.values() if x['status'] == 'OPTIMAL'), None) for nm, d in by.items()}
    supported = lambda t: [r for r in R if r['tool'] == t and r['status'] != 'UNSUPPORTED']
    matched = [nm for nm, d in by.items() if all(t in d and d[t]['status'] == 'OPTIMAL' for t in tools)]
    print(f'{len(by)} targets, {len(tools)} tools, matched (all solved) {len(matched)}, size conflicts {len(conflicts)}')
    for c in conflicts[:10]:
        print('  CONFLICT', c)
    hdr = f"{'tool':22} {'solved':>9} {'wrong':>5} {'PAR-2':>10} {'matched tot':>11} {'matched med':>11} {'SAT s':>9} {'UNSAT s':>9} {'peak MB':>8}"
    print(hdr)
    cactus = {}
    for t in tools:
        S = supported(t)
        if not S:
            continue
        dl = S[0]['deadline']
        solved = [r for r in S if r['status'] == 'OPTIMAL']
        wrong = sum(r['status'] in ('WRONG', 'ERROR') or (r['status'] == 'OPTIMAL' and r.get('verified') is False) for r in S)
        par2 = sum(r['seconds'] if r['status'] == 'OPTIMAL' else 2 * dl for r in S) / len(S)
        mt = [by[nm][t]['seconds'] for nm in matched]
        sat_s = sum(b[2] for r in S for b in r['budgets'] if b[1] == 'SAT')
        uns_s = sum(b[2] for r in S for b in r['budgets'] if b[1] == 'UNSAT')
        peak = max((r.get('peak_mb') or 0) for r in S)
        cactus[t] = sorted(r['seconds'] for r in solved)
        print(f"{t:22} {len(solved):>4}/{len(S):<4} {wrong:>5} {par2:>10.3f} {sum(mt):>11.2f} "
              f"{(statistics.median(mt) if mt else 0):>11.4f} {sat_s:>9.2f} {uns_s:>9.2f} {peak:>8.1f}")
    key = opt.get('--by', 'n')
    groups = defaultdict(list)
    for nm, d in by.items():
        any_r = next(iter(d.values()))
        g = any_r['n'] if key == 'n' else size_of[nm] if key == 'size' else any_r.get('family')
        groups[g].append(nm)
    print(f'\nsolved / PAR-2 by {key}:')
    for g in sorted(groups, key=lambda x: (x is None, x)):
        names = groups[g]
        cells = []
        for t in tools:
            rs = [by[nm][t] for nm in names if t in by[nm] and by[nm][t]['status'] != 'UNSUPPORTED']
            if not rs:
                cells.append(f'{t}=n/a'); continue
            dl = rs[0]['deadline']
            ok = sum(r['status'] == 'OPTIMAL' for r in rs)
            p2 = sum(r['seconds'] if r['status'] == 'OPTIMAL' else 2 * dl for r in rs) / len(rs)
            cells.append(f'{t}={ok}/{len(rs)},{p2:.2f}')
        print(f'  {key}={g} ({len(names)}): ' + '  '.join(cells))
    stem = os.path.splitext(path)[0]
    json.dump(cactus, open(stem + '_cactus.json', 'w'), indent=0)


if __name__ == '__main__':
    main()
