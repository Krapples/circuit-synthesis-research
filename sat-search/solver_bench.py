"""Compare SAT solvers on hard pieces with the current --fast encoding. The cap is enforced by killing the
worker pool (CaDiCaL ignores interrupts; Kissat runs through a rebuild wrapper), so every solver is timed
the same way. Every finished piece is appended to solver_bench_results.jsonl at once; at the end the
best single solver is compared with the per-piece best (an optimistic portfolio bound).
Default: range-2 graph #77 at exactly 14 gates, its 11 lowest-index orbit-least pieces.
Usage: python solver_bench.py [cap] [graph_index] [npieces] [solvers,comma,separated] [extra k=v,...]"""
import json, os, sys, time
from multiprocessing import Pool
import cube_search as cs

DEFAULT_SOLVERS = 'maplechrono,maplecm,glucose42,mergesat3,cadical195'   # cadical300, kissat404: far slower even on C5
FACTOR = 1.5   # early stop: a solver is cut once it runs FACTOR x the best complete time so far
FAST = dict(sens=True, units=True, usens=True, bypass=True, elim=True, elimclosure=True, signeddom=True,
            recursivebounds=True, recdepth=2, notbypass=True)


def stat(stats, key):
    try:
        return float(stats.split(key + '=')[1].split()[0].rstrip('s'))
    except Exception:
        return None


if __name__ == '__main__':
    cap = float(sys.argv[1]) if len(sys.argv) > 1 else 240
    gi = int(sys.argv[2]) if len(sys.argv) > 2 else 77
    npieces = int(sys.argv[3]) if len(sys.argv) > 3 else 11
    solvers = (sys.argv[4] if len(sys.argv) > 4 and sys.argv[4] else DEFAULT_SOLVERS).split(',')
    extra = {}
    if len(sys.argv) > 5 and sys.argv[5]:
        for kv in sys.argv[5].split(','):
            k, v = kv.split('=')
            extra[k] = int(v) if v.isdigit() else v == 'True'
    flags = {**FAST, **extra}
    g = json.load(open('range2_graphs.json'))[gi]
    n, edges, G = g['n'], [tuple(e) for e in g['edges']], g['bound'] - 1
    masks = [(1 << u) | (1 << v) for u, v in edges]
    auts = cs.automorphisms(n, edges)
    allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)] + [(2, i, i) for i in range(n)]
    pieces = sorted((c for c in allc if cs.orbit_min(c, auts)), key=lambda c: (c[2], c[1], c[0]))[:npieces]
    out = open('solver_bench_results.jsonl', 'a', encoding='utf-8')
    print(f'graph #{gi}: exactly {G} gates, pieces {pieces}, flags {sorted(k for k, v in flags.items() if v)}, '
          f'cap {cap:.0f}s per solver (pool killed at cap)', flush=True)
    table = {}
    best_wall = None
    for solver in solvers:
        t0 = time.time()
        limit = cap if best_wall is None else min(cap, FACTOR * best_wall)
        print(f'{time.strftime("%H:%M:%S")} {solver}', flush=True)
        p = Pool(len(pieces))
        res = {c: p.apply_async(cs.run_cube, ((n, masks, G, solver, c, True, True, flags),)) for c in pieces}
        seen = set()
        while True:
            for c, r in res.items():
                if c in seen or not r.ready():
                    continue
                seen.add(c)
                try:
                    cube, st, circ, dt, stats = r.get()
                except Exception as e:
                    st, dt, stats = f'ERROR {e}', 0.0, ''
                rec = dict(graph=gi, G=G, solver=solver, cube=list(c), status=st, seconds=round(dt, 1),
                           conflicts=stat(stats, 'conflicts'), iters=stat(stats, 'iters'), rows=stat(stats, 'rows'),
                           solve=stat(stats, 'solve'))
                out.write(json.dumps(rec) + '\n'); out.flush()
                table[solver, c] = rec
                cps = (rec['conflicts'] or 0) / max(rec['solve'] or dt, 1e-9)
                print(f'   {c}: {st} in {dt:.0f}s  conflicts={rec["conflicts"]}  conflicts/s={cps:,.0f}  '
                      f'iters={rec["iters"]}  rows={rec["rows"]}', flush=True)
            if len(seen) == len(pieces) or time.time() - t0 >= limit:
                break
            time.sleep(0.5)
        p.terminate(); p.join()
        fin = [table[solver, c] for c in pieces if (solver, c) in table and table[solver, c]['status'] == 'UNSAT']
        if any(table.get((solver, c), {}).get('status') == 'WITNESS' for c in pieces):
            print('   !!! WITNESS reported', flush=True)
        timed_out = [c for c in pieces if (solver, c) not in table]
        if not timed_out and len(fin) == len(pieces):
            w = time.time() - t0
            best_wall = w if best_wall is None else min(best_wall, w)
        elif time.time() - t0 >= limit and limit < cap:
            print(f'   stopped early at {limit:.0f}s ({FACTOR}x the best time so far)', flush=True)
        print(f'  => {solver}: {len(fin)}/{len(pieces)} UNSAT, {len(timed_out)} timed out at {cap:.0f}s; '
              f'wall {min(time.time() - t0, cap):.0f}s; CPU of finished {sum(r["seconds"] for r in fin):.0f}s; '
              f'slowest finished {max((r["seconds"] for r in fin), default=0):.0f}s', flush=True)
    # portfolio analysis: pieces finished by every solver vs per-piece best
    print('PORTFOLIO (cap counts for unfinished pieces):', flush=True)
    tot = {}
    for solver in solvers:
        tot[solver] = sum(table[solver, c]['seconds'] if (solver, c) in table and table[solver, c]['status'] == 'UNSAT'
                          else cap for c in pieces)
        print(f'   {solver:12s} total {tot[solver]:6.0f}s', flush=True)
    best = min(tot, key=tot.get)
    port = sum(min((table[s_, c]['seconds'] if (s_, c) in table and table[s_, c]['status'] == 'UNSAT' else cap)
                   for s_ in solvers) for c in pieces)
    winners = {}
    for c in pieces:
        w = min(solvers, key=lambda s_: table[s_, c]['seconds'] if (s_, c) in table and table[s_, c]['status'] == 'UNSAT' else cap)
        winners[w] = winners.get(w, 0) + 1
    print(f'   best single solver: {best} ({tot[best]:.0f}s); per-piece best portfolio: {port:.0f}s '
          f'({tot[best] / max(port, 1e-9):.2f}x better); per-piece winners: {winners}', flush=True)
