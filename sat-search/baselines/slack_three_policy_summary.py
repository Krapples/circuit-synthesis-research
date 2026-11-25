"""Summarize a first_layer_check screen jsonl per mode (slack-three lazy policy stats)."""
import json
import sys
from collections import defaultdict

rows = [json.loads(line) for path in sys.argv[1:] for line in open(path, encoding='utf-8') if line.strip()]
modes = []
stats = defaultdict(lambda: defaultdict(float))
unsat8 = defaultdict(list)
minima = defaultdict(dict)
for row in rows:
    mode = row['mode']
    if mode not in modes:
        modes.append(mode)
    s = stats[mode]
    s['wall'] += row['wall_seconds']
    s['peak'] = max(s['peak'], row['peak_bytes'] / 2 ** 20)
    for record in row['records']:
        if 'k' in record:
            s['conflicts'] += record.get('conflicts', 0)
            if record['k'] == 7 and record['status'] == 'UNSAT':
                s['excl7'] += 1
            if record['k'] == 8:
                s['conf8'] += record.get('conflicts', 0)
                if record['status'] == 'UNSAT':
                    s['unsat8'] += 1
                    unsat8[mode].append(row['tt'])
                elif record['status'] == 'SAT':
                    s['sat8'] += 1
            for key in ('slack_three_seconds', 'three_cuts', 'three_repeats', 'three_clause_literals',
                        'three_extension_total', 'three_tight_calls', 'three_slack_one_calls',
                        'three_slack_two_calls', 'three_threshold_cuts', 'three_covered', 'three_memo_hits',
                        'slack_three_pure', 'slack_three_conditional', 'slack_three_seen', 'slack_three_unknown',
                        'three_extension_excluded', 'three_extension_unknown'):
                s[key] += record.get(key, 0)
            for level, count in enumerate(record.get('three_lift', []), 1):
                s[f'lift{level}'] += count
        if record.get('final') == 'SAT':
            minima[mode][row['tt']] = record['steps']
            s['minima'] += 1

print('| Mode | Size-7 excl | Size-8 SAT / UNSAT | Conflicts | Size-8 conflicts | Minima | Wall s | Peak MiB |')
print('| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |')
for mode in modes:
    s = stats[mode]
    print(f"| {mode} | {s['excl7']:.0f} | {s['sat8']:.0f} / {s['unsat8']:.0f} | {s['conflicts']:,.0f} | "
          f"{s['conf8']:,.0f} | {s['minima']:.0f} | {s['wall']:.1f} | {s['peak']:.1f} |")
print()
print('| Mode | Cuts | Repeats | Lift 1/2/3/4 | Literals/cut | Ext calls | Ext total | Avoided | Covered | Memo hits | Slack-three s |')
print('| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |')
for mode in modes:
    s = stats[mode]
    if not s['three_cuts'] and not s['slack_three_seen']:
        continue
    calls = s['three_tight_calls'] + s['three_slack_one_calls'] + s['three_slack_two_calls']
    cuts = s['three_cuts'] or 1
    lifts = '/'.join(f"{s[f'lift{i}']:.0f}" for i in range(1, 5))
    print(f"| {mode} | {s['three_cuts']:.0f} | {s['three_repeats']:.0f} | {lifts} | "
          f"{s['three_clause_literals'] / cuts:.1f} | {calls:,.0f} | {s['three_extension_total']:,.0f} | "
          f"{s['three_extension_total'] - calls:,.0f} | {s['three_covered']:,.0f} | {s['three_memo_hits']:,.0f} | "
          f"{s['slack_three_seconds']:.1f} |")
print()
for mode in modes:
    print(mode, 'size-8 UNSAT:', ' '.join(sorted(unsat8[mode])))
base = None
for mode in modes:
    if base is None:
        base = minima[mode]
        continue
    lost = sorted(t for t in base if t not in minima[mode])
    gained = sorted(t for t in minima[mode] if t not in base)
    for t in set(base) & set(minima[mode]):
        assert base[t] == minima[mode][t], (t, mode)
    print(mode, 'minima vs', modes[0], 'lost', lost, 'gained', gained)
