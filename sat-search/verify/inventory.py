"""Per-rule coverage inventory from the differential records (results/differential/*.jsonl).

For each configuration it counts passing, failing and open jobs in four semantic classes:
  whole-min    whole function at G = M (must be SAT) and G = M - 1 (must be UNSAT);
  whole-exact  whole function at G = M + 1 (reference verdict), M + 2 and M + 4 (SAT by padding);
  prefix-min   pinned prefix at G = M_P and M_P - 1;
  prefix-exact pinned prefix at G = M_P + 2 and M_P + 4 (SAT: padding keeps the prefix);
plus command-line (production entry point) jobs and non-graph families. Open (timed-out) jobs count as
neither pass nor fail. Status per configuration:
  failed      any wrong verdict in any class;
  tested      every class has passing jobs and no failures (independently tested on finite instances, not a
              proof; the rule's own proof status is recorded separately in verify/AUDIT.md);
  unresolved  some class has no passing coverage.
Writes verify/coverage_inventory.json (consumed by the default-combination guard) and prints a table.
Usage: python verify/inventory.py [run files...]"""
import glob, json, os, sys
from collections import defaultdict
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import differential as dif

CLASSES = ('whole-min', 'whole-exact', 'prefix-min', 'prefix-exact')


def classify(r, M, MP=None):
    G = r['G']
    if not r['prefix']:
        if M is None:
            return None
        return 'whole-min' if G in (M - 1, M) else 'whole-exact' if G > M else None
    if r.get('expect') == 'UNSAT':
        return 'prefix-min'
    return 'prefix-min' if MP is None or G == MP else 'prefix-exact'


def main(files):
    cache = dif.load_ref_cache()
    pmin = {}
    pc = os.path.join(ROOT, 'results', 'reference_prefix_minima.jsonl')
    if os.path.exists(pc):
        for line in open(pc, encoding='utf-8'):
            x = json.loads(line)
            k = json.loads(x['key'])
            pmin[(k[1], tuple(k[2]), k[3], tuple(tuple(g) for g in k[4]))] = x['prefix_minimum']
    # Later records of the same job replace earlier ones (files in modification order), so a rerun after a fix
    # supersedes the records of the defective version; every run file records its source hash in its header.
    latest, cli_latest, versions = {}, {}, []
    for f in sorted(files, key=os.path.getmtime):
        for line in open(f, encoding='utf-8'):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get('header'):
                versions.append((os.path.basename(f), r.get('version')))
                continue
            if 'flags' in r and 'prefix' not in r:                               # CLI records
                cli_latest[(r['config'], r['n'], tuple(r['terms']), r['basis'], r['G'])] = r
                continue
            if 'prefix' not in r:
                continue
            latest[(r['config'], r['n'], tuple(r['terms']), r['basis'], r['G'], tuple(map(tuple, r['prefix'])))] = r
    stats = defaultdict(lambda: defaultdict(lambda: [0, 0, 0]))     # config -> class -> [pass, fail, open]
    extra = defaultdict(lambda: dict(cli=[0, 0, 0], nongraph=0, contract_rejections=0))
    for r in cli_latest.values():
        extra[r['config']]['cli'][0 if r['ok'] else 1 if r['ok'] is False else 2] += 1
    for r in latest.values():
        if True:
            if r.get('contract') and r['verdict'] == 'ERROR':
                extra[r['config']]['contract_rejections'] += 1
                continue
            refr = cache.get((r['n'], tuple(r['terms']), r['basis']))
            M = refr['minimum'] if refr else None
            P = tuple(map(tuple, r['prefix']))
            MP = None
            if P:
                MP = next((v for (n, t, b, q), v in pmin.items()
                           if (n, t, b, q) == (r['n'], tuple(r['terms']), r['basis'], P) and v is not None), None)
                if r['expect'] == 'SAT' and MP is None:
                    MP = r['G']           # base-run prefix jobs are recorded at M_P itself
            c = classify(r, M, MP)
            if c is None:
                continue
            s = stats[r['config']][c]
            s[0 if r['ok'] else 1 if r['ok'] is False else 2] += 1
            if r['kind'] != 'graph' and r['ok']:
                extra[r['config']]['nongraph'] += 1
    inv = {}
    for cfg in sorted(set(stats) | set(extra)):
        cl = {c: stats[cfg][c] for c in CLASSES}
        fails = sum(v[1] for v in cl.values()) + extra[cfg]['cli'][1]
        harness = any(cl[c][0] for c in CLASSES)
        if fails:
            status = 'failed'
        elif cfg.endswith('minimal'):
            # valid only for whole functions at G <= M (prerequisite enforced); prefixes are disabled (R2)
            status = 'tested (whole-min only, by design)' if cl['whole-min'][0] else 'unresolved'
        elif not harness:
            status = 'tested (command line, whole function)' if extra[cfg]['cli'][0] else 'unresolved'
        else:
            status = 'tested' if all(cl[c][0] > 0 for c in CLASSES) else 'unresolved'
        inv[cfg] = dict(status=status, classes=cl, **extra[cfg],
                        missing=[c for c in CLASSES if cl[c][0] == 0])
    json.dump(dict(files=[os.path.relpath(f, ROOT) for f in files], run_versions=versions, configs=inv),
              open(os.path.join(HERE, 'coverage_inventory.json'), 'w', encoding='utf-8'), indent=1)
    print(f'{"configuration":24} {"status":38} ' + ' '.join(f'{c:>16}' for c in CLASSES) +
          f' {"CLI":>12} {"non-graph":>9}')
    for cfg, v in inv.items():
        cells = ' '.join(f'{"%d/%d/%d" % tuple(v["classes"][c]):>16}' for c in CLASSES)
        print(f'{cfg:24} {v["status"]:38} {cells} {"%d/%d/%d" % tuple(v["cli"]):>12} {v["nongraph"]:9}')
    print('cells: pass/fail/open')
    return inv


if __name__ == '__main__':
    files = sys.argv[1:] or sorted(glob.glob(os.path.join(ROOT, 'results', 'differential', '*.jsonl')))
    files = [f for f in files if not os.path.basename(f).startswith(('smoke', 'limit-smoke', 'cache-smoke',
                                                                      'padded-smoke', 'cli-smoke'))]
    main(files)
