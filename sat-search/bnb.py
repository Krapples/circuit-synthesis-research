"""Adaptive analytical branch-and-bound over pinned prefixes (monotone exact-G model).

A node is a pinned prefix P (gates 0..k-1) at exact size G; its claim is "no exact-G every-wire-read circuit
begins with P" (under the colex order cube_search applies after the prefix, colex_from = k at the root).
Children of P are all next gates (op, l, r), l < r < n + k, allowed by the colex order relative to the last
gate when k > colex_from (keys (r, l) nondecreasing) -- exactly the gates the encoding admits, so the split
is exhaustive. A node is closed
  analytically  when max(forced-repeat bound, ordered prefix bound) > G (bounds from cube_search; the repeat
                bound reuses the parent's projections; ordered bounds are cached on the multiset of feature
                columns, which determines them);
  by SAT        when cube_search.run_cube with the prefix pinned returns UNSAT within the conflict budget;
and is refuted when SAT returns a witness (checked on every row). Policy: extend a node while the fraction
of its children closed analytically is at least --min-reject and the feature count stays within the ordered
bound's limit; otherwise give it to SAT; a SAT timeout is split once more if possible, else left open.
The tree is appended to a JSONL file (one record per node event) and resumes from it.
Usage: python bnb.py --n N --edges ... --size G [--seed-prefix op,l,r;...] [--colex-from K] [--workers 20]"""
import argparse, hashlib, json, os, sys, time
from multiprocessing import Pool
import cube_search as cs

FEATURE_LIMIT = cs.PARTIAL_FEATURE_LIMIT


def children(n, prefix, colex_from):
    j = n + len(prefix)
    last = prefix[-1] if len(prefix) > colex_from else None
    out = []
    for r in range(j):
        for l in range(r):
            if last is not None and (r, l) < (last[2], last[1]):
                continue
            out.extend(((0, l, r), (1, l, r)))
    return out


def feature_key(n, masks, prefix):
    """Canonical key for the ordered bound: multiset of (column on boundary rows, mandatory flag)."""
    mandatory, pos, neg = cs.prefix_boundary(n, masks, tuple(prefix))
    width = n + len(prefix)
    cols = []
    for i in range(width):
        col = tuple(r >> i & 1 for r in pos) + tuple(r >> i & 1 for r in neg)
        cols.append((col, mandatory >> i & 1))
    return tuple(sorted(cols))


_ORD = {}


def analytical(args):
    n, masks, prefix, G = args
    t0 = time.time()
    rep = cs.partial_repeat_bound(n, masks, tuple(prefix[:-1]), prefix[-1]) if len(prefix) > 1 else 0
    if rep > G:
        return prefix, 'repeat', rep, time.time() - t0
    if n + len(prefix) > FEATURE_LIMIT:
        return prefix, None, rep, time.time() - t0
    key = feature_key(n, masks, prefix)
    if key not in _ORD:
        _ORD[key] = cs.ordered_prefix_bound(n, masks, tuple(prefix))
    b = max(rep, _ORD[key])
    return prefix, 'ordered' if b > G else None, b, time.time() - t0


def sat(args):
    n, masks, prefix, G, flags, seconds = args
    import tempfile, threading
    stop = os.path.join(tempfile.gettempdir(), f'bnb_STOP_{os.getpid()}')
    cs.STOP = stop
    timer = threading.Timer(seconds, lambda: open(stop, 'w').close())
    timer.start()
    try:
        fl = dict(flags, colex_from=len(prefix), fixgates=[(i, *g) for i, g in enumerate(prefix[1:], 1)])
        _, st, circ, dt, info = cs.run_cube((n, list(masks), G, 'maplechrono', tuple(prefix[0]), False, False, fl))
    finally:
        timer.cancel()
        timer.join()
        if os.path.exists(stop):
            os.remove(stop)
    ok = None
    if st == 'WITNESS':
        ok = all(cs.evaluate(n, circ, x) == any(x & m == m for m in masks) for x in range(1 << n))
    return prefix, st, circ, ok, round(dt, 2), str(info)[:200]


def tree_scope(n, masks, size, seed, colex_from, root_children):
    return dict(n=n, masks=list(masks), size=size, seed=[list(gate) for gate in seed],
                colex_from=colex_from, root_children=bool(root_children or not seed))


def read_tree(path, scope):
    """Reuse evidence only from a segment with the same mathematical scope."""
    closed = {}
    scoped = False
    if os.path.exists(path):
        with open(path, encoding='utf-8') as stream:
            for line in stream:
                record = json.loads(line)
                if record.get('kind') == 'scope':
                    if record.get('scope') != scope:
                        raise ValueError('resume file belongs to a different target, budget, or prefix scope')
                    scoped = True
                    continue
                if not scoped:
                    continue
                if record.get('G') != scope['size']:
                    raise ValueError('resume record has a different gate budget')
                status = record.get('status')
                if status in ('analytical', 'sat-unsat', 'expanded') or status == 'witness' and record.get('verified'):
                    closed[tuple(map(tuple, record['prefix']))] = status
    return closed, scoped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--edges', required=True)
    ap.add_argument('--size', type=int, required=True)
    ap.add_argument('--seed-prefix', default='', help='pinned root prefix, e.g. "1,6,9;1,7,10;0,11,12"')
    ap.add_argument('--colex-from', type=int, default=None, help='colex order applies from this gate (default: root length)')
    ap.add_argument('--root-children', action='store_true', help='start from the children of the seed prefix')
    ap.add_argument('--min-reject', type=float, default=0.8)
    ap.add_argument('--sat-seconds', type=float, default=120)
    ap.add_argument('--workers', type=int, default=20)
    ap.add_argument('--tree', default=None)
    a = ap.parse_args()
    n = a.n
    edges = [tuple(map(int, e.split('-'))) for e in a.edges.split(',')]
    masks = tuple(sorted({(1 << u) | (1 << v) for u, v in edges}))
    seed = [tuple(map(int, g.split(','))) for g in a.seed_prefix.split(';') if g]
    colex_from = a.colex_from if a.colex_from is not None else len(seed)
    flags = {'nonot': True, **{k: True for k in ('sens', 'usens', 'bypass', 'elim', 'elimclosure', 'signeddom',
                                                    'recursivebounds', 'notbypass', 'recclosure', 'identifybounds',
                                                    'fanoutelim', 'pairro', 'colorbounds', 'sharecolor',
                                                    'colorbudget', 'partialordered', 'partialrepeat')}, 'recdepth': 2}
    scope = tree_scope(n, masks, a.size, seed, colex_from, a.root_children)
    fingerprint = hashlib.sha256(json.dumps(scope, sort_keys=True).encode()).hexdigest()[:12]
    tree_path = a.tree or os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results',
                                       f'bnb_n{n}_G{a.size}_{fingerprint}.jsonl')
    try:
        closed, scoped = read_tree(tree_path, scope)
    except ValueError as error:
        ap.error(str(error))
    tree = open(tree_path, 'a', encoding='utf-8')
    if not scoped:
        tree.write(json.dumps(dict(kind='scope', scope=scope)) + '\n')
        tree.flush()

    def record(prefix, **kw):
        tree.write(json.dumps(dict(prefix=[list(g) for g in prefix], G=a.size, **kw)) + '\n'); tree.flush()

    frontier = [tuple(seed + [c]) for c in children(n, seed, colex_from)] if a.root_children or not seed else [tuple(seed)]
    t0 = time.time()
    stats = dict(analytical=0, sat_unsat=0, open=0, expanded=0, witness=0)
    for state in closed.values():
        stats[state.replace('-', '_')] += 1
    with Pool(a.workers) as p:
        while frontier:
            # resume: walk through previously expanded nodes to their children; skip other closed nodes
            while any(closed.get(P) == 'expanded' for P in frontier):
                frontier = [Q for P in frontier for Q in
                            ([tuple(list(P) + [c]) for c in children(n, list(P), colex_from)]
                             if closed.get(P) == 'expanded' else [P])]
            todo = [P for P in frontier if P not in closed]
            frontier = []
            res = p.map(analytical, [(n, masks, list(P), a.size) for P in todo])
            survivors = []
            for prefix, rule, bound, dt in res:
                P = tuple(prefix)
                if rule:
                    record(P, status='analytical', rule=rule, bound=bound); closed[P] = 'analytical'
                    stats['analytical'] += 1
                else:
                    survivors.append((P, bound))
            print(f'[{time.time() - t0:.0f}s] level: {len(todo)} nodes, {len(todo) - len(survivors)} closed '
                  f'analytically, {len(survivors)} survive', flush=True)
            to_sat, to_split = [], []
            for P, bound in survivors:
                kids = children(n, list(P), colex_from)
                deeper_ok = n + len(P) + 1 <= FEATURE_LIMIT and len(P) + 1 < a.size
                if deeper_ok:
                    probe = p.map(analytical, [(n, masks, list(P) + [c], a.size) for c in kids[:min(len(kids), 40)]])
                    rate = sum(1 for _, rule, _, _ in probe if rule) / max(1, len(probe))
                    if rate >= a.min_reject:
                        to_split.append(P); continue
                to_sat.append(P)
            for P in to_split:
                record(P, status='expanded'); closed[P] = 'expanded'; stats['expanded'] += 1
                frontier.extend(tuple(list(P) + [c]) for c in children(n, list(P), colex_from))
            if to_sat:
                for prefix, st, circ, ok, dt, info in p.imap_unordered(
                        sat, [(n, masks, list(P), a.size, flags, a.sat_seconds) for P in to_sat]):
                    P = tuple(prefix)
                    if st == 'UNSAT':
                        record(P, status='sat-unsat', seconds=dt, info=info); closed[P] = 'sat-unsat'
                        stats['sat_unsat'] += 1
                    elif st == 'WITNESS' and ok:
                        record(P, status='witness', circuit=circ, verified=ok); closed[P] = 'witness'
                        stats['witness'] += 1
                        print(f'WITNESS under prefix {P}: verified={ok}', flush=True)
                    else:
                        record(P, status='open', seconds=dt); stats['open'] += 1
            print(f'[{time.time() - t0:.0f}s] {stats}', flush=True)
    print(f'RESULT {stats} ({time.time() - t0:.0f}s)', flush=True)
    tree.close()


if __name__ == '__main__':
    main()
