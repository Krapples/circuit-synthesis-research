"""L-meta-1343 shard 2 (first three gates x6|x9, x7|x10, their AND), monotone, sizes 14..21, cube_search --fast.
Two cases cover the shard:
 (a) the seed AND is used: pin all three seed gates (ordering rule from gate n+3), pieces on gate n+3, size G;
 (b) the seed AND is unused: dropping it leaves a valid circuit of size G-1 starting x6|x9, x7|x10: pin those
     two (ordering rule from gate n+2), pieces on gate n+2, size G-1.
Sizes <= 13 (both cases) were already UNSAT with mono_shard.py (results/l1343_shard2.log).
Early stop: a size is abandoned if it runs longer than max(120 s, 5 x the previous size's wall time).
Usage: python l1343_full.py [Gmin] [Gmax] [reuse] [logfile] [extra flags, comma-separated]"""
import json, sys, time
from multiprocessing import Pool
import cube_search as cs

EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
         (6, 7), (6, 10), (7, 9), (8, 9)]
n = 11
MASKS = [(1 << u) | (1 << v) for u, v in EDGES]
FAST = dict(sens=True, units=True, usens=True, bypass=True, elim=True, elimclosure=True, signeddom=True,
            recursivebounds=True, recdepth=2, notbypass=True, recclosure=True, identifybounds=True,
            fanoutelim=True, pairro=True, colorbounds=True, sharecolor=True, colorbudget=True, nonot=True)


def tasks_for(G):
    out = []
    ja = n + 3      # case (a)
    for c in [(op, l, r) for r in range(ja) for l in range(r) for op in (0, 1)]:
        out.append(('a', G, c, (n, MASKS, G, 'maplechrono', (1, 6, 9), True, True,
                                {**FAST, 'colex_from': 3, 'fixgates': [(1, 1, 7, 10), (2, 0, 11, 12), (3, *c)]})))
    jb = n + 2      # case (b), size G - 1
    for c in [(op, l, r) for r in range(jb) for l in range(r) for op in (0, 1)]:
        out.append(('b', G, c, (n, MASKS, G - 1, 'maplechrono', (1, 6, 9), True, True,
                                {**FAST, 'colex_from': 2, 'fixgates': [(1, 1, 7, 10), (2, *c)]})))
    return out


def run(t):
    case, G, c, args = t
    return case, G, c, cs.run_cube(args)


if __name__ == '__main__':
    g0 = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    g1 = int(sys.argv[2]) if len(sys.argv) > 2 else 21
    REUSE = len(sys.argv) > 3 and sys.argv[3] == 'reuse'
    if REUSE:
        FAST['reuse'] = True
    log = open(sys.argv[4] if len(sys.argv) > 4 else 'results/l1343_shard2_fast.log', 'a', encoding='utf-8')
    EXTRA = [x for x in (sys.argv[5].split(',') if len(sys.argv) > 5 else []) if x]
    RACE = 'race' in EXTRA
    EXTRA = [x for x in EXTRA if x != 'race']
    for x in EXTRA:
        FAST[x] = True
    if 'orderedports' in EXTRA or 'monoports' in EXTRA:
        FAST['portcosts'] = cs.port_costs(cs._anti(MASKS), mono='monoports' in EXTRA, separation='monoports' in EXTRA)

    def say(m):
        line = f'{time.strftime("%H:%M:%S")} {m}'
        print(line, flush=True); log.write(line + '\n'); log.flush()
    say(f'L-meta-1343 shard 2, sizes {g0}..{g1}, monotone, cube_search --fast; case (a) seed used, case (b) seed AND '
        f'unused (size G-1); edges {EDGES}; persistent solvers: {REUSE}; extra {EXTRA}')
    prev = None
    for G in range(g0, g1 + 1):
        tasks = tasks_for(G)
        limit = max(120.0, 5 * prev) if prev else 3600.0
        p = Pool(22); t0 = time.time()
        res = [p.apply_async(run, (t,)) for t in tasks]
        done = 0; unsat = 0; wit = None; slow = 0.0
        pending = list(range(len(res)))
        race = {}                  # straggler racing: piece index -> async results of other solvers
        last_done = time.time()

        def finished(k):
            """A piece is settled when its own run or any racing copy has returned UNSAT or WITNESS."""
            if res[k].ready():
                return res[k].get()
            for r in race.get(k, ()):
                if r.ready():
                    out = r.get()
                    if out[3][1] in ('UNSAT', 'WITNESS'):
                        return out
            return None
        while pending and time.time() - t0 < limit and wit is None:
            for k in list(pending):
                out = finished(k)
                if out is not None:
                    pending.remove(k); last_done = time.time()
                    case, GG, c, (cube, st, circ, dt, stats) = out
                    done += 1; slow = max(slow, dt)
                    if st == 'UNSAT':
                        unsat += 1
                    elif st == 'WITNESS':
                        size = G if case == 'a' else G - 1
                        ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in MASKS) for x in range(1 << n))
                        say(f'!!! WITNESS case {case} size {size} piece {c} verified={ok}: {circ}')
                        if ok:
                            wit = (case, c, circ)
                    else:
                        say(f'piece {case}{c} size {G}: {st}')
                    if done % 50 == 0:
                        say(f'size {G}: {done}/{len(tasks)} pieces done (elapsed {time.time() - t0:.0f}s)')
            # Racing: once only a few pieces remain and nothing has finished for a while, the other cores are
            # idle; give each straggler copies on other solvers (any solver's UNSAT is a valid proof).
            if RACE and len(pending) <= 5 and time.time() - last_done > 30:
                for k in pending:
                    if k not in race:
                        case, GG, c, args = tasks[k]
                        fl = {kk: vv for kk, vv in args[7].items() if kk != 'reuse'}
                        race[k] = [p.apply_async(run, ((case, GG, c, (*args[:3], sv, *args[4:7], fl)),))
                                   for sv in ('glucose42', 'maplecm', 'cadical195', 'mergesat3')]
                        say(f'size {G}: racing straggler {case}{c} on 4 more solvers')
            time.sleep(0.2)
        p.terminate(); p.join()
        wall = time.time() - t0
        if wit:
            say(f'RESULT size {G}: circuit found, see above'); break
        if pending:
            say(f'size {G}: STOPPED at {limit:.0f}s with {done}/{len(tasks)} pieces done ({unsat} UNSAT); not finished')
            break
        if unsat != len(tasks):
            say(f'size {G}: finished but only {unsat}/{len(tasks)} pieces UNSAT (others stopped or errored); not a proof')
            break
        say(f'size {G}: ALL {len(tasks)} pieces UNSAT (case a: {sum(1 for t in tasks if t[0] == "a")}, case b: '
            f'{sum(1 for t in tasks if t[0] == "b")}) in {wall:.0f}s, slowest piece {slow:.0f}s')
        prev = wall
    say('done')
