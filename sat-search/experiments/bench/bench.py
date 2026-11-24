"""Solver benchmark with early stopping.

Every (instance, solver, seed) runs as its own subprocess, 11 at a time. Within each
(instance, seed) group, once the first solver finishes in time B, every other solver in that group
gets B + GRACE seconds of its own run time and is then killed and recorded as CUT. A hard limit
still applies. Killing the process is reliable; the solvers' own interrupt is not.
Finished results from earlier logs (--resume) are reused, not rerun.

Scores: wins (fastest in a group), median time where finished, cuts, and a capped total in
which a cut counts at its cut time (a lower bound on what it would have taken).

Usage: python bench.py [--grace 30] [--limit 1500] [--seeds 3] [--resume old.log] [--log bench.log]
"""
import argparse, os, re, statistics, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
JOB = os.path.join(HERE, 'bench_job.py')

ap = argparse.ArgumentParser()
ap.add_argument('--grace', type=float, default=30)
ap.add_argument('--limit', type=float, default=1500)
ap.add_argument('--seeds', type=int, default=3)
ap.add_argument('--instances', default='fano13and,fano13or,m1343a,m1343b')
ap.add_argument('--solvers', default='maplechrono,maplecm,glucose4,glucose42,mergesat3,cadical195')
ap.add_argument('--workers', type=int, default=11)
ap.add_argument('--resume', action='append', default=[])
ap.add_argument('--log', default=os.path.join(HERE, 'bench.log'))
a = ap.parse_args()
log = open(a.log, 'a', encoding='utf-8')


def say(msg):
    line = f'{time.strftime("%H:%M:%S")} {msg}'
    print(line, flush=True); log.write(line + '\n'); log.flush()


insts, solvers = a.instances.split(','), a.solvers.split(',')
results = {}                      # job -> (status, seconds)
LINE = re.compile(r'\] (\S+)\s+(\S+)\s+seed (\d+): (SAT|UNSAT)\s+([\d.]+)s')
for path in a.resume:
    for line in open(path, encoding='utf-8'):
        m = LINE.search(line)
        if m and m.group(1) in insts and m.group(2) in solvers:
            results[(m.group(1), m.group(2), int(m.group(3)))] = (m.group(4), float(m.group(5)))

best = {}                          # (inst, seed) -> fastest finished time
for (i, s, seed), (st, x) in results.items():
    best[i, seed] = min(best.get((i, seed), 1e18), x)

jobs = [(i, s, seed) for seed in range(a.seeds) for i in insts for s in solvers if (i, s, seed) not in results]
total = len(jobs) + len(results)
say(f'benchmark: {len(insts)} instances x {len(solvers)} solvers x {a.seeds} seeds = {total} jobs '
    f'({len(results)} reused from earlier logs); {a.workers} at a time; early stop at best + {a.grace:.0f}s; '
    f'hard limit {a.limit:.0f}s')

running = {}                       # job -> (Popen, start)
done = len(results)


def finish(job, status, secs, note=''):
    global done
    done += 1
    results[job] = (status, secs)
    say(f'[{done}/{total}] {job[0]:10s} {job[1]:12s} seed {job[2]}: {status:7s} {secs:7.1f}s{note}')


def cutoff(job):
    b = best.get((job[0], job[2]))
    return min(a.limit, b + a.grace) if b is not None else a.limit


while jobs or running:
    # skip queued jobs whose group already finished so fast that the grace is shorter than startup
    while jobs and len(running) < a.workers:
        job = jobs.pop(0)
        p = subprocess.Popen([sys.executable, JOB, *map(str, job)], stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, env={**os.environ, 'OMP_NUM_THREADS': '1'})
        running[job] = (p, time.time())
    time.sleep(0.5)
    for job, (p, t0) in list(running.items()):
        el = time.time() - t0
        if p.poll() is not None:
            out, err = p.communicate()
            del running[job]
            line = next((l for l in out.splitlines() if l.startswith('RESULT')), None)
            if line is None:
                finish(job, 'ERROR', el, '  ' + ' '.join((err or '').strip().splitlines()[-1:]))
                continue
            st, secs = line.split()[4], float(line.split()[5])
            g = (job[0], job[2])
            first = g not in best or secs < best[g]
            best[g] = min(best.get(g, 1e18), secs)
            finish(job, st, secs, '  (fastest in its group so far)' if first else '')
        elif el > cutoff(job):
            p.kill(); p.communicate()
            del running[job]
            b = best.get((job[0], job[2]))
            finish(job, 'CUT' if b is not None and el < a.limit else 'TIMEOUT', el,
                   f'  (best was {b:.1f}s)' if b is not None else '')

say(f'SUMMARY (grace {a.grace:.0f}s). Per instance: median finished time, and +nC = cut n times')
score = {}
for s in solvers:
    cells, capped, wins, cuts = [], 0.0, 0, 0
    for i in insts:
        r = [results.get((i, s, seed), ('MISSING', 0.0)) for seed in range(a.seeds)]
        ok = [x for st, x in r if st in ('SAT', 'UNSAT')]
        nc = sum(1 for st, _ in r if st not in ('SAT', 'UNSAT'))
        cuts += nc
        capped += sum(x for _, x in r)
        for seed in range(a.seeds):
            st, x = results.get((i, s, seed), ('MISSING', 0))
            if st in ('SAT', 'UNSAT') and x <= best.get((i, seed), 1e18) + 1e-9:
                wins += 1
        cells.append((f'{statistics.median(ok):6.0f}' if ok else '     -') + (f' +{nc}C' if nc else '    '))
    score[s] = (wins, -cuts, -capped)
    say(f'  {s:12s} ' + ' '.join(cells) + f'   wins {wins:2d}  cuts {cuts:2d}  capped total {capped:7.0f}s')
say('  columns: ' + ', '.join(insts))
say('RANKING (most wins, then fewest cuts, then lowest capped total): '
    + ' > '.join(sorted(solvers, key=lambda s: score[s], reverse=True)))
