"""Search-order benchmark for ordered_quotient_core.solve3 on the quotient_bench.py targeted excess-three cores
(construction tasks). Each order runs in its own process with a hard deadline. Exclusion-task timings
come from results/excess3_ladder.jsonl (cores with result None).
Writes results/quotient_order_bench.jsonl. Usage: python experiments/quotient_order_bench.py [deadline]"""
import json, os, sys, time
import multiprocessing as mp
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
for d in ('', 'theory'):
    sys.path.insert(0, os.path.join(HERE, d))


def run(q, n, f, signed, internal_first):
    from ordered_quotient_core import solve3, materialize3
    t = time.time(); a = solve3(n, f, signed, internal_first=internal_first); dt = time.time() - t
    G, _ = materialize3(n, f, a, signed)
    q.put(dict(n=n, f=hex(f), signed=signed, internal_first=internal_first, result=a[0], gates=len(G), seconds=round(dt, 3)))


if __name__ == '__main__':
    deadline = float(sys.argv[1]) if len(sys.argv) > 1 else 120
    import io, contextlib
    from quotient_bench import targeted
    with contextlib.redirect_stdout(io.StringIO()):
        fs = targeted()
    out = open(os.path.join(HERE, 'results', 'quotient_order_bench.jsonl'), 'w', encoding='utf-8')
    q = mp.Queue(); ps = []
    for n, f, signed in fs:
        for o in (False, True):
            p = mp.Process(target=run, args=(q, n, f, signed, o)); p.start(); ps.append((p, n, f, signed, o))
    t0 = time.time(); got = 0
    while got < len(ps) and time.time() - t0 < deadline:
        while not q.empty():
            r = q.get(); got += 1; out.write(json.dumps(r) + '\n'); out.flush(); print(r, flush=True)
        time.sleep(0.1)
    for p, n, f, signed, o in ps:
        if p.is_alive():
            p.terminate(); out.write(json.dumps(dict(n=n, f=hex(f), signed=signed, internal_first=o, status='timeout')) + '\n')
            print('TIMEOUT', hex(f), o, flush=True)
        p.join()
