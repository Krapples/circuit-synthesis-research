"""Resume a cube_search.py run with finer pieces, or fill the cores an old run leaves idle.

Resume mode (old run stopped):
* Reads earlier logs (--from-log) and skips every piece already marked UNSAT.
* Splits every unfinished first-gate piece by the SECOND gate too (about 100 parts each), so no
  single job can run for hours and the cores do not sit idle at the end of the run.
* Hardest pieces first (gates on low-numbered inputs).
* Each worker keeps one solver for its whole life and only changes the assumptions between
  parts, so clauses it learned (and counterexample rows) carry over from part to part.
  That is sound: everything added to the solver holds for every circuit, whatever the cube.

Sharing mode (--share-log, old run still going): a tail-filler.
* Waits until the old run starts leaving workers idle (all its pieces handed out and some
  finished), then races the old run's unfinished pieces, split finer, on the idle cores only:
  it never has more parts running than the old run has idle workers (re-checked every 30 s).
* Re-reads the old log; parts whose piece the old run finished are skipped.
* When every piece is UNSAT in one log or the other, or either run finds a circuit, it creates
  the old run's STOP file (--share-stop) so the old run's redundant stragglers exit too.

Stop safely by creating STOP (stops both runs) or STOP_FILLER (stops only this one).
Lines it writes are in cube_search.py's format, so any log can be fed back with --from-log.

Usage:
  python cube_resume.py --n 9 --edges ... --size 11 --from-log old.log --log resume.log
  python cube_resume.py --n 9 --edges ... --size 11 --share-log old.log --log filler.log
"""
import argparse, os, re, sys, threading, time
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')
import queue
from multiprocessing import Pool
from cube_search import build, evaluate, STOP, HERE   # also puts the bundled pysat on sys.path
from pysat.solvers import Solver

STOP_FILLER = os.path.join(HERE, 'STOP_FILLER')
CUBE = r'\((\d+), (\d+), (\d+)\)'
LINE = re.compile(rf'cube {CUBE}(?:/{CUBE})?: UNSAT')
HEADER = re.compile(r'(\d+) cubes, (\d+) workers')
OPS = {0: 'AND', 1: 'OR', 2: 'NOT'}


def gates(m):
    """All (op, left, right) for a gate reading wires 0..m-1, as the encoding allows them."""
    return [(op, l, r) for op in (0, 1) for r in range(m) for l in range(r)] + [(2, i, i) for i in range(m)]


def hardness(c):
    op, l, r = c
    return (r, l, op)          # low-numbered inputs were by far the slowest in the first run


def read_log(path):
    """-> dict(done1, done2, total, workers, witness, finished) from a cube_search/cube_resume log."""
    d = dict(done1=set(), done2=set(), total=None, workers=None, witness=False, finished=False)
    try:
        with open(path, encoding='utf-8') as f:
            for line in f:
                m = LINE.search(line)
                if m:
                    g = tuple(map(int, m.groups()[:3]))
                    if m.group(4) is None:
                        d['done1'].add(g)
                    else:
                        d['done2'].add((g, tuple(map(int, m.groups()[3:]))))
                elif d['total'] is None and (h := HEADER.search(line)):
                    d['total'], d['workers'] = map(int, h.groups())
                if 'WITNESS verified=True' in line:
                    d['witness'] = True
                if 'RESULT:' in line:
                    d['finished'] = True
    except FileNotFoundError:
        pass
    return d


def idle_old_workers(d):
    if d['finished']:
        return d['workers']
    return len(d['done1']) - (d['total'] - d['workers'])


_W = {}


def init(n, masks, G, solver_name, stops):
    output, pool, clauses, ops, select = build(n, G)
    target = lambda x: any(x & m == m for m in masks)
    s = Solver(name=solver_name, bootstrap_with=clauses)
    N = 1 << n

    def row(x):
        val = [pool.id(('val', x, j)) for j in range(output + 1)]
        yield from ([val[i] if x >> i & 1 else -val[i]] for i in range(n))
        for j, (a, o, no) in ops.items():
            l, r = [pool.id(('arg', x, j, k)) for k in range(2)]
            for k, arg in enumerate((l, r)):
                for i, sel in enumerate(select[j, k]):
                    yield [-sel, -arg, val[i]]
                    yield [-sel, arg, -val[i]]
            f = val[j]
            yield from ([-a, -l, -r, f], [-a, l, -f], [-a, r, -f], [-o, l, r, -f], [-o, -l, f],
                        [-o, -r, f], [-no, -l, -f], [-no, l, f])
        yield [val[-1] if target(x) else -val[-1]]

    rows = {0, N - 1, *masks, *(1 << i for i in range(n))}
    rows |= {x for x in range(N) if not target(x)
             and all(target(x | 1 << i) for i in range(n) if not x >> i & 1)}
    for x in rows:
        s.append_formula(list(row(x)))

    def watch():
        while True:
            time.sleep(5)
            if any(os.path.exists(p) for p in stops):
                s.interrupt()
                return
    threading.Thread(target=watch, daemon=True).start()
    _W.update(n=n, N=N, target=target, s=s, row=row, rows=rows, ops=ops, select=select,
              stops=stops)


def run_part(part):
    c1, c2 = part
    w = _W; n, s, ops, select = w['n'], w['s'], w['ops'], w['select']
    if any(os.path.exists(p) for p in w['stops']):
        return part, 'STOPPED', None, 0.0
    t0 = time.time()
    assume = [ops[n][c1[0]], select[n, 0][c1[1]], select[n, 1][c1[2]],
              ops[n + 1][c2[0]], select[n + 1, 0][c2[1]], select[n + 1, 1][c2[2]]]
    while True:
        res = s.solve_limited(assumptions=assume, expect_interrupt=True)
        if res is None:
            return part, 'STOPPED', None, time.time() - t0
        if not res:
            return part, 'UNSAT', None, time.time() - t0
        m = set(s.get_model())
        c = [(next(k for k, v in enumerate(ops[j]) if v in m),
              *(next(i for i, v in enumerate(select[j, k]) if v in m) for k in range(2))) for j in ops]
        bad = [x for x in range(w['N']) if evaluate(n, c, x) != w['target'](x)]
        if not bad:
            return part, 'WITNESS', c, time.time() - t0
        for x in bad:
            s.append_formula(list(w['row'](x)))
        w['rows'].update(bad)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--edges', required=True)
    ap.add_argument('--size', type=int, required=True)
    ap.add_argument('--from-log', action='append', default=[])
    ap.add_argument('--share-log', default=None, help="a still-running cube_search.py run's log")
    ap.add_argument('--share-stop', default=STOP, help="the old run's STOP file")
    ap.add_argument('--extra', type=int, default=0,
                    help='sharing mode: parts to run on top of the old run idle workers (spare SMT threads); '
                         'with --extra, pieces go in REVERSE of the old run order, so the two runs meet in the middle')
    ap.add_argument('--log', default=None)
    ap.add_argument('--workers', type=int, default=11)
    ap.add_argument('--solver', default='maplechrono')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    n = a.n
    edges = [tuple(map(int, e.split('-'))) for e in a.edges.split(',')]
    masks = [(1 << u) | (1 << v) for u, v in edges]
    log = open(a.log, 'a', encoding='utf-8') if a.log and not a.dry_run else None

    def say(msg):
        line = f'{time.strftime("%H:%M:%S")} {msg}'
        print(line, flush=True)
        if log:
            log.write(line + '\n'); log.flush()

    share = a.share_log
    stops = [STOP_FILLER, a.share_stop] if share else [STOP]
    if share:
        if os.path.exists(STOP_FILLER):
            os.remove(STOP_FILLER)
        say(f'tail-filler for {share}: waiting until its workers go idle. '
            f'Stop only this run with: create file {STOP_FILLER}')
        last = 0
        while True:
            if os.path.exists(STOP_FILLER) or os.path.exists(a.share_stop):
                say('RESULT: STOPPED before starting'); return
            d = read_log(share)
            if d['witness'] or d['finished']:
                say(f'RESULT: old run already ended ({"witness" if d["witness"] else "finished"}); nothing to do')
                return
            if idle_old_workers(d) >= 1 or a.extra > 0:
                break
            if time.time() - last > 600:
                say(f'old run: {len(d["done1"])}/{d["total"]} pieces done; its workers start going idle '
                    f'after {d["total"] - d["workers"]} (still waiting)')
                last = time.time()
            time.sleep(60)
        a.from_log.append(share)

    done1, done2 = set(), set()
    for path in a.from_log:
        d = read_log(path)
        done1 |= d['done1']; done2 |= d['done2']
    all1 = gates(n)
    if share and a.extra:       # old run hands pieces out in gates(n) order: start from its far end
        firsts = [c for c in all1[::-1] if c not in done1]
    else:
        firsts = sorted((c for c in all1 if c not in done1), key=hardness)
    seconds = sorted(gates(n + 1), key=hardness)
    parts = [(c1, c2) for c1 in firsts for c2 in seconds if (c1, c2) not in done2]
    left = {c1: sum(1 for p in parts if p[0] == c1) for c1 in firsts}

    say(f'{"tail-filler" if share else "resume"}: n={n}, {len(edges)} edges, exactly {a.size} gates; '
        f'{len(done1)} of {len(all1)} first-gate pieces already UNSAT, {len(firsts)} left, split into '
        f'{len(parts)} parts ({len(done2)} parts already UNSAT); up to {a.workers} workers'
        f'{f" ({a.extra} extra + the old run idle ones)" if share else ""}, {a.solver}.')
    say('first-gate pieces left, in order: ' + ', '.join(f'{OPS[c[0]]}{c[1:]}' for c in firsts))
    if a.dry_run or not parts:
        say('RESULT: ' + ('dry run, nothing solved' if parts else 'ALL UNSAT (nothing left)'))
        return
    if not share and os.path.exists(STOP):
        os.remove(STOP)
    say(f'Stop with: create file {stops[0]}')

    def stop_old(why):
        if share:
            open(a.share_stop, 'w').close()
            say(f'{why}: created {a.share_stop} so the old run exits too')

    t0 = time.time(); done = 0; skipped = 0; result = 'ALL UNSAT'; mine = set()
    pending = list(parts); inflight = 0; results = queue.Queue(); d = None; checked = 0
    allowed = a.workers
    with Pool(a.workers, initializer=init, initargs=(n, masks, a.size, a.solver, stops)) as p:
        while pending or inflight:
            if share and time.time() - checked > 30:
                d = read_log(share); checked = time.time()
                allowed = min(a.workers, a.extra + max(0, idle_old_workers(d)))
                if d['witness']:
                    result = 'old run found a WITNESS'; break
            while pending and inflight < allowed:
                part = pending.pop(0)
                if share and part[0] in d['done1']:
                    skipped += 1; done += 1
                    if skipped % 100 == 1:
                        say(f'skipping parts of pieces the old run finished ({skipped} so far)')
                    continue
                p.apply_async(run_part, (part,), callback=results.put,
                              error_callback=lambda e: results.put(e))
                inflight += 1
            try:
                r = results.get(timeout=5)
            except queue.Empty:
                continue
            inflight -= 1
            if isinstance(r, BaseException):
                raise r
            (c1, c2), status, circ, dt = r
            done += 1
            el = time.time() - t0
            eta = el / max(done - skipped, 1) * (len(parts) - done)
            say(f'[{done}/{len(parts)}] cube {c1}/{c2}: {status} in {dt:.0f}s '
                f'(elapsed {el:.0f}s, {inflight} running, rough ETA {eta / 3600:.1f}h)')
            if status == 'WITNESS':
                ok = all(evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
                say(f'WITNESS verified={ok}: {circ}')
                result = 'WITNESS'; stop_old('circuit found'); break
            if status == 'STOPPED':
                result = 'STOPPED'; break
            left[c1] -= 1
            if left[c1] == 0:
                say(f'cube {c1}: UNSAT (all parts)')
                mine.add(c1)
            if share:
                d = read_log(share); checked = time.time()
                if len(done1 | d['done1'] | mine) == len(all1):
                    stop_old('every piece is UNSAT in one log or the other'); break
        else:
            if share:
                stop_old('every piece is UNSAT in one log or the other')
        p.terminate()
    say(f'RESULT: {result} (exactly {a.size} gates) after {time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
