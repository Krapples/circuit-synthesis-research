"""Scan L-meta-519 range-2 graphs (range2_graphs.json) for a counterexample: a circuit with fewer than
E + tau - 1 gates. For each graph, exact sizes bound-1 and bound-2 (padding by 2 covers all smaller sizes),
every orbit-least first-gate piece, all pieces of all graphs in one pool. Only rules implied for every
circuit (fanout, readonce, sens, units) plus the symmetry breaking; no minimality rules.
Logs one line per finished (graph, size) and a loud line for any WITNESS (verified on all inputs).

Usage: python range2_scan.py [--workers 22] [--nmax 11] [--log range2_scan.log]"""
import argparse, json, time
from multiprocessing import Pool
import cube_search as cs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=22)
    ap.add_argument('--nmax', type=int, default=11)
    ap.add_argument('--log', default='range2_scan.log')
    a = ap.parse_args()
    log = open(a.log, 'a', encoding='utf-8')

    def say(msg):
        line = f'{time.strftime("%H:%M:%S")} {msg}'
        print(line, flush=True); log.write(line + '\n'); log.flush()

    graphs = [g for g in json.load(open('range2_graphs.json')) if g['n'] <= a.nmax]
    tasks, left = [], {}
    for gi, g in enumerate(graphs):
        n, edges = g['n'], [tuple(e) for e in g['edges']]
        masks = [(1 << u) | (1 << v) for u, v in edges]
        auts = cs.automorphisms(n, edges)
        allc = [(op, l, r) for op in (0, 1) for r in range(n) for l in range(r)] + [(2, i, i) for i in range(n)]
        cubes = [c for c in allc if cs.orbit_min(c, auts)]
        for G in (g['bound'] - 1, g['bound'] - 2):
            left[gi, G] = len(cubes)
            for c in cubes:
                tasks.append(((gi, G), (n, masks, G, 'maplechrono', c, True, True, dict(sens=True, units=True))))
    say(f'range-2 scan: {len(graphs)} graphs (n <= {a.nmax}), {len(tasks)} pieces, {a.workers} workers')
    t0 = time.time(); found = 0; started = {}
    with Pool(a.workers) as p:
        it = p.imap_unordered(job, tasks)
        for (key, (cube, status, circ, dt, stats)) in it:
            gi, G = key; g = graphs[gi]
            if status == 'WITNESS':
                n = g['n']; masks = [(1 << u) | (1 << v) for u, v in g['edges']]
                ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
                say(f'!!! WITNESS verified={ok}: graph #{gi} n={n} edges={g["edges"]} E={g["E"]} tau={g["tau"]} '
                    f'bound={g["bound"]}, circuit with {G} gates: {circ}')
                found += 1
            elif status != 'UNSAT':
                say(f'piece {cube} of graph #{gi} size {G}: {status}')
            left[key] -= 1
            if left[key] == 0:
                say(f'graph #{gi} n={g["n"]} E={g["E"]} tau={g["tau"]} cycles={g["cycles"]} size {G} (bound {g["bound"]}): '
                    f'done (elapsed {time.time() - t0:.0f}s)')
    say(f'RESULT: {found} counterexample circuit(s) found across {len(graphs)} graphs after {time.time() - t0:.0f}s')


def job(t):
    key, args = t
    return key, cs.run_cube(args)


if __name__ == '__main__':
    main()
