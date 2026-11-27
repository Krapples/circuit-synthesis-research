"""Independent witness check: simulate tree_dp gates on every cared row of the unit, bit by bit."""
import json, sys
units = {}
for line in open(sys.argv[1]):
    p = line.split()
    if p: units[p[0]] = (int(p[1]), [(int(a, 16), int(b)) for a, b in (x.split(':') for x in p[5].split(','))])
ok = bad = 0
for d in map(json.loads, open(sys.argv[2])):
    if d.get('min_k') is None: continue
    n, rows = units[d['id']]
    good = len(d['gates']) == d['min_k']
    for r, t in rows:
        w = [r >> i & 1 for i in range(n)]
        for op, a, b in d['gates']:
            assert a < len(w) and b < len(w)
            w.append(w[a] & w[b] if op == 0 else w[a] | w[b])
        good &= w[d['output']] == t
    ok += good; bad += not good
    if not good: print('BAD', d['id'])
print(f'witness ok {ok} bad {bad}')
