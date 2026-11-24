"""Compare encoder versions on hard pieces of a hard instance, each version capped at CAP seconds
(the cap creates the STOP file; MapleChrono honours interrupts). Default: range-2 graph #77
(n=11, E=11, tau=5, bound 15), exactly 14 gates, its 11 lowest-index orbit-least pieces.
Usage: python hard_bench.py [cap] [graph_index] [npieces]"""
import importlib, json, os, sys, threading, time
from multiprocessing import Pool

CONFIGS = [('--fast (v15)', 'cube_search', {}),
           ('+activecolor +colorzero +isolatedcolor', 'cube_search', dict(activecolor=True, colorzero=True, isolatedcolor=True)),
           ('+portbounds', 'cube_search', dict(portbounds=True)),
           ('all v16', 'cube_search', dict(activecolor=True, colorzero=True, isolatedcolor=True, portbounds=True))]
FAST = dict(sens=True, units=True, usens=True, bypass=True, elim=True, elimclosure=True, signeddom=True,
            recursivebounds=True, recdepth=2, notbypass=True, recclosure=True, identifybounds=True, fanoutelim=True,
            pairro=True, colorbounds=True, sharecolor=True, colorbudget=True)
FACTOR = 1.5   # stop a configuration at FACTOR x the best complete wall time so far (pool killed)


def job(t):
    modname, args = t
    mod = importlib.import_module(modname)
    return mod.run_cube(args)


if __name__ == '__main__':
    cap = float(sys.argv[1]) if len(sys.argv) > 1 else 300
    gi = int(sys.argv[2]) if len(sys.argv) > 2 else 77
    npieces = int(sys.argv[3]) if len(sys.argv) > 3 else 11
    import cube_search as cs
    g = json.load(open('range2_graphs.json'))[gi]
    n, edges, G = g['n'], [tuple(e) for e in g['edges']], g['bound'] - 1
    masks = [(1 << u) | (1 << v) for u, v in edges]
    auts = cs.automorphisms(n, edges)
    allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)] + [(2, i, i) for i in range(n)]
    pieces = sorted((c for c in allc if cs.orbit_min(c, auts)), key=lambda c: (c[2], c[1], c[0]))[:npieces]
    print(f'graph #{gi}: n={n} E={g["E"]} tau={g["tau"]} bound={g["bound"]} -> exactly {G} gates; '
          f'{len(auts)} automorphisms; pieces {pieces}; cap {cap:.0f}s per version', flush=True)
    best = None
    pc = cs.port_costs(cs._anti(masks))
    for name, modname, extra in CONFIGS:
        if extra.get('portbounds'):
            extra = {**extra, 'portcosts': pc}
        limit = cap if best is None else min(cap, FACTOR * best)
        t0 = time.time(); fin = []; cpu = 0.0; conf = 0
        print(f'{time.strftime("%H:%M:%S")} {name} (limit {limit:.0f}s)', flush=True)
        p = Pool(len(pieces))
        res = {c: p.apply_async(job, ((modname, (n, masks, G, 'maplechrono', c, True, True, {**FAST, **extra})),))
               for c in pieces}
        seen = set()
        while len(seen) < len(pieces) and time.time() - t0 < limit:
            for c, r in res.items():
                if c not in seen and r.ready():
                    seen.add(c)
                    cube, st, circ, dt, stats = r.get()
                    cc = int(stats.split('conflicts=')[1].split()[0]) if 'conflicts=' in stats else 0
                    cpu += dt; conf += cc
                    if st == 'UNSAT':
                        fin.append(c)
                    print(f'   {cube}: {st} in {dt:.0f}s  conflicts={cc:,}  {stats if "analytical" in stats else ""}', flush=True)
                    if st == 'WITNESS':
                        print('   !!! WITNESS', circ, flush=True)
            time.sleep(0.3)
        p.terminate(); p.join()
        wall = time.time() - t0
        if len(fin) == len(pieces):
            best = wall if best is None else min(best, wall)
            print(f'  => {len(fin)}/{len(pieces)} UNSAT; wall {wall:.0f}s; CPU {cpu:.0f}s; conflicts {conf / 1e6:.2f}M', flush=True)
        else:
            print(f'  => stopped at {limit:.0f}s with {len(fin)}/{len(pieces)} UNSAT (CPU of finished {cpu:.0f}s)', flush=True)
