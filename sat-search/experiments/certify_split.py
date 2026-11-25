"""Parallel certification of exact-size exclusions, split exhaustively by the first gate.

In the exact-G model every circuit has a gate 0 (wire n): an AND/OR of two distinct inputs, or (general
basis) NOT of an input. Pinning gate 0 to each option gives an exhaustive set of independent pieces; each is
solved by the independent reference encoder with a DRUP proof checked by the RUP checker. All pieces
UNSAT = exact size G certified UNSAT. A piece that times out leaves the exclusion open (never counted).
Items: (case, basis, M) whose exclusions at M-1 and M-2 are to be certified; M from
results/module_core_minima.jsonl and results/first_gate_compare.jsonl (hypergraph-07).
Writes results/certified_exclusions.jsonl (one line per (case, basis, G)).
Usage: python experiments/certify_split.py [workers] [seconds_per_piece] [max_n]"""
import json, os, sys, time
from collections import defaultdict
from multiprocessing import Pool
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'verify', 'experiments'):
    sys.path.insert(0, os.path.join(HERE, d))
import reference as ref
from certify_synthesis import check_proof
from signed_bound_compare import cases, restrict_essential


def first_gates(n, basis):
    out = [(op, l, r) for r in range(n) for l in range(r) for op in (0, 1)]
    if basis == 'general':
        out += [(2, a, a) for a in range(n)]
    return out


def piece(job):
    name, basis, n, f, G, gate, seconds = job
    t0 = time.time()
    w, info = ref.sat_exists(n, f, G, basis, (gate,), proof=True, seconds=seconds)
    if info.get('undecided'):
        return job, 'open', round(time.time() - t0, 1), None
    if w is not None:
        return job, 'SAT', round(time.time() - t0, 1), w
    if info.get('trivial'):
        return job, 'checked_unsat', 0.0, 0
    proof = list(info['proof'])
    if not proof or proof[-1].split() != ['0']:
        proof.append('0')
    steps = check_proof(info['vars'], info['cnf'], proof)
    return job, 'checked_unsat', round(time.time() - t0, 1), steps


if __name__ == '__main__':
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 3600
    max_n = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    targets = {}
    for line in open(os.path.join(HERE, 'results', 'module_core_minima.jsonl'), encoding='utf-8'):
        r = json.loads(line)
        for basis in ('general', 'monotone'):
            if r.get(f'{basis}_witness_verified') is True:
                targets[(r['case'], basis)] = r[f'{basis}_min']
    for line in open(os.path.join(HERE, 'results', 'first_gate_compare.jsonl'), encoding='utf-8'):
        r = json.loads(line)
        if not r.get('partial') and r.get('upper') is not None and r['total'] >= r['upper'] > r['best_prior']:
            targets.setdefault((r['case'], 'general'), r['upper'])
    done = set()
    path = os.path.join(HERE, 'results', 'certified_exclusions.jsonl')
    if os.path.exists(path):
        for line in open(path, encoding='utf-8'):
            r = json.loads(line)
            if r['status'] == 'CERTIFIED':
                done.add((r['case'], r['basis'], r['G']))
    jobs, meta = [], {}
    for name, fam, n0, f0 in cases():
        n, f, _ = restrict_essential(n0, f0)
        for basis in ('general', 'monotone'):
            M = targets.get((name, basis))
            if M is None or n > max_n:
                continue
            for G in (M - 1, M - 2):
                if G < n - 1 or (name, basis, G) in done:
                    continue
                gates = first_gates(n, basis)
                meta[(name, basis, G)] = dict(n=n, pieces=len(gates), results={})
                jobs += [(name, basis, n, f, G, g, seconds) for g in gates]
    # hardest (largest n, largest G) first so the long tail starts early
    jobs.sort(key=lambda j: (-j[2], -j[4]))
    print(f'{len(meta)} exclusions, {len(jobs)} first-gate pieces, {workers} workers', flush=True)
    out = open(path, 'a', encoding='utf-8')
    t0 = time.time()
    with Pool(workers) as p:
        for job, status, dt, extra in p.imap_unordered(piece, jobs):
            name, basis, n, f, G, gate, _ = job
            m = meta[(name, basis, G)]
            m['results'][gate] = (status, dt)
            if status == 'SAT':
                print(f'!!! {name} {basis} size {G}: piece {gate} SAT -> minimum claim contradicted: {extra}', flush=True)
            if len(m['results']) == m['pieces']:
                sts = [s for s, _ in m['results'].values()]
                grade = 'CERTIFIED' if all(s == 'checked_unsat' for s in sts) else \
                    'CONTRADICTION' if 'SAT' in sts else 'open'
                rec = dict(case=name, basis=basis, n=n, G=G, status=grade, pieces=m['pieces'],
                           open_pieces=sts.count('open'), seconds=round(sum(d for _, d in m['results'].values()), 1))
                out.write(json.dumps(rec) + '\n'); out.flush()
                print(f'{name} {basis} size {G}: {grade} ({m["pieces"]} pieces, {rec["seconds"]}s CPU) '
                      f'[{time.time() - t0:.0f}s]', flush=True)
    print('DONE', flush=True)
