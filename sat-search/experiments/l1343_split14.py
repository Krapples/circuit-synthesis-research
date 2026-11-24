"""Does splitting finer make L-meta-1343 shard 2 faster at size 14?

Takes the same 11 size-14 pieces as l1343_quicktest.py (split on the first free gate; there 3 of 11
finished within 15 minutes) and splits each again on the next gate. Each worker keeps one MapleChrono
solver (exact mode + duplicate-gate ban) and changes only the assumptions between parts.
Logs every finished piece with its total core time; stops at --cap seconds of wall time.

Usage: python l1343_split14.py [--cap 1800] [--plain] [--log l1343_split14.log]
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))  # sat-search/
import argparse, time
from multiprocessing import Pool
import mono_shard as m

_W = {}


def init(G, distinct):
    from pysat.solvers import Solver
    pool, cl, isand, sel, outv, first = m.build(G, True, distinct)
    _W.update(s=Solver(name='maplechrono', bootstrap_with=cl), isand=isand, sel=sel, first=first)


def lit(op, g):
    return _W['isand'][g] if op == 0 else -_W['isand'][g]


def part(args):
    c1, c2 = args
    w = _W; j = w['first']; t = time.time()
    a = [w['sel'][j][0][c1[1]], w['sel'][j][1][c1[2]], lit(c1[0], j),
         w['sel'][j + 1][0][c2[1]], w['sel'][j + 1][1][c2[2]], lit(c2[0], j + 1)]
    res = w['s'].solve(assumptions=a)
    return c1, c2, res, time.time() - t


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--cap', type=float, default=1800)
    ap.add_argument('--plain', action='store_true', help='without the duplicate-gate ban')
    ap.add_argument('--log', default='l1343_split14.log')
    ap.add_argument('--workers', type=int, default=11)
    a = ap.parse_args()
    log = open(a.log, 'a', encoding='utf-8')

    def say(msg):
        line = f'{time.strftime("%H:%M:%S")} {msg}'
        print(line, flush=True); log.write(line + '\n'); log.flush()

    G = 14
    j = m.N_IN + len(m.SEED)
    firsts = [(op, l, r) for r in range(j) for l in range(r) for op in (0, 1)][:11]
    seconds = [(op, l, r) for r in range(j + 1) for l in range(r) for op in (0, 1)]
    # interleave pieces so every piece progresses in parallel and finishes roughly together
    parts = [(c1, c2) for c2 in seconds for c1 in firsts]
    left = {c1: len(seconds) for c1 in firsts}; core = {c1: 0.0 for c1 in firsts}
    say(f'size {G}: {len(firsts)} pieces x {len(seconds)} second-gate choices = {len(parts)} parts, '
        f'{a.workers} workers, maplechrono, {"plain" if a.plain else "duplicate-gate ban"}, cap {a.cap:.0f}s')
    t0 = time.time(); done = 0; status = 'ALL 11 PIECES UNSAT'
    with Pool(a.workers, initializer=init, initargs=(G, not a.plain)) as p:
        for c1, c2, res, dt in p.imap_unordered(part, parts):
            done += 1; left[c1] -= 1; core[c1] += dt
            if res:
                status = f'MODEL in {c1}/{c2} (unexpected; check)'; say(status); p.terminate(); break
            if left[c1] == 0:
                say(f'piece {c1}: UNSAT, all {len(seconds)} parts, {core[c1]:.0f} core-seconds '
                    f'(wall {time.time() - t0:.0f}s)')
            if done % max(1, len(parts) // 100) == 0:
                say(f'{100 * done // len(parts)}% ({done}/{len(parts)} parts) done (wall {time.time() - t0:.0f}s)')
            if time.time() - t0 > a.cap:
                status = f'CAPPED at {a.cap:.0f}s with {done}/{len(parts)} parts done'
                p.terminate(); break
        p.terminate()
    tot = sum(core.values())
    say(f'RESULT: {status}; wall {time.time() - t0:.0f}s, total core time {tot:.0f}s; '
        f'pieces finished: {sum(1 for c in firsts if left[c] == 0)}/{len(firsts)}')
    for c1 in firsts:
        say(f'  piece {c1}: {len(seconds) - left[c1]}/{len(seconds)} parts, {core[c1]:.0f} core-s')
