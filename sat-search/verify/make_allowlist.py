"""Generate sat-search/verified_combinations.json: the command-line rule combinations with complete
whole-function differential coverage.

The active rule set of each tested flag set is taken from the production command line itself
(`cube_search.py ... --dry-run --allow-unverified` prints it after every implication), not re-derived here.
A combination is admitted only if verify/coverage_inventory.json shows, for that flag set,
  * command-line jobs: at least one pass and no failure, and
  * when the run_cube harness has a configuration of the same name: passing whole-min and whole-exact jobs
    and no failure in any class.
The command line only searches whole functions, so the prefix classes are not required here; drivers that
pin prefixes must check the prefix classes in the inventory themselves.
Usage: python verify/make_allowlist.py"""
import json, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from cli_differential import FLAGSETS

CLI = os.path.join(ROOT, 'cube_search.py')


def active_rules(flags, basis):
    cmd = [sys.executable, CLI, '--n', '4', '--edges', '0-1,1-2,2-3', '--size', '4', '--workers', '1', '--dry-run',
           '--allow-unverified', *flags.split()] + (['--monotone'] if basis == 'monotone' else [])
    out = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT).stdout
    m = re.search(r'active rules \((\w+)\): (\[.*\])', out)
    if not m:
        raise RuntimeError(f'no active-rules line for {flags!r}: {out[-300:]}')
    return json.loads(m.group(2).replace("'", '"'))


if __name__ == '__main__':
    inv = json.load(open(os.path.join(HERE, 'coverage_inventory.json'), encoding='utf-8'))['configs']
    combos, rejected = [], []
    for name, (flags, bases) in sorted(FLAGSETS.items()):
        v = inv.get(name)
        reasons = []
        if v is None or v['cli'][0] == 0:
            reasons.append('no passing command-line jobs')
        elif v['cli'][1]:
            reasons.append('command-line failures')
        if v is not None and any(v['classes'][c][0] for c in v['classes']):     # harness configuration exists
            # --minimal is valid only at G <= M (prerequisite enforced from manifests), so it needs whole-min only
            for c in (('whole-min',) if name.endswith('minimal') else ('whole-min', 'whole-exact')):
                if v['classes'][c][0] == 0:
                    reasons.append(f'no passing {c} jobs')
            if any(x[1] for x in v['classes'].values()):
                reasons.append('harness failures')
        for basis in (('monotone', 'general') if bases == 'both' else (bases,)):
            rules = active_rules(flags, basis)
            if not rules:
                continue
            if reasons:
                rejected.append(dict(name=name, basis=basis, rules=rules, reasons=reasons))
            elif rules not in [c['rules'] for c in combos]:
                combos.append(dict(name=name, basis=basis, rules=rules,
                                   evidence=dict(cli=v['cli'], classes=v['classes'])))
    out = dict(generated_by='verify/make_allowlist.py', inventory_files=json.load(
        open(os.path.join(HERE, 'coverage_inventory.json'), encoding='utf-8'))['files'],
        scope='whole-function command-line runs', combinations=combos, rejected=rejected)
    json.dump(out, open(os.path.join(ROOT, 'verified_combinations.json'), 'w', encoding='utf-8'), indent=1)
    print(f'{len(combos)} verified combinations, {len(rejected)} rejected')
    for r in rejected:
        print(f'  rejected {r["name"]} ({r["basis"]}): {", ".join(r["reasons"])}')
