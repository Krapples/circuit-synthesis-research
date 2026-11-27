"""Turn a circuit found by any SAT search into the Lean proof file for a pequalnp desk step.

The step statement is read from a desk gaps snapshot (or passed with --statement); the shapes are
those parsed by template_synth.parse (RepSizeAtMost rectangles, two-lit FanInTwo/Monotone2, and
Represents inside an existential). The circuit is re-simulated in Python with the Lean semantics of
PEqualNP.CircuitLowerBounds (missing wire reads false, NOT of no input is true, AND of none is true)
on every row the statement quantifies over, and its gate kinds, fan-in and size are checked, before
any file is written.

Circuit formats (gate j writes wire n + j; output defaults to the last gate):
  --gates "OR(1,2), NOT(7), AND(0,8)"            text as in desk sketches
  --gates '[[1,10,11],[0,2,18]]'                 rep-sat.py records: [op, left, right], 0=AND 1=OR 2=NOT
  --gates '[["or",[1,2]],["not",[7]]]'           template_synth tuples
  --record file.jsonl                             first SAT record with "gates" (and "output")

Usage:
  python desk_lean_emit.py --gaps gaps.json --id L-meta-21782 --gates "OR(0,4), ..." [--output 17] \
      [--out lean/PEqualNP/Outside/L_meta_21782.lean]
Without --out the file is printed. Exit status 1 and no file if the circuit is wrong.
"""
import argparse, json, re, sys

from template_synth import parse, simulate, lean_file

OPS = {0: 'and', 1: 'or', 2: 'not', 'and': 'and', 'or': 'or', 'not': 'not'}


def parse_gates(text):
    text = text.strip()
    if text.startswith('['):
        out = []
        for g in json.loads(text):
            if isinstance(g[0], str) and isinstance(g[1], list):
                out.append((OPS[g[0].lower()], list(g[1])))
            else:
                op = OPS[g[0]]
                out.append((op, [g[1]] if op == 'not' else list(g[1:3])))
        return out
    out = []
    for op, args in re.findall(r'(AND|OR|NOT)\s*\(([^)]*)\)', text, re.I):
        out.append((op.lower(), [int(a) for a in args.split(',') if a.strip()]))
    if not out:
        raise SystemExit('no gates parsed from: %r' % text[:80])
    return out


def check(spec, gates, out):
    """Return a list of problems (empty if the circuit proves the statement)."""
    bad = []
    if len(gates) > spec['size']:
        bad.append('%d gates > budget %d' % (len(gates), spec['size']))
    for j, (op, ins) in enumerate(gates):
        if op == 'not' and not spec['general']:
            bad.append('gate %d is NOT but the statement is monotone' % j)
        if len(ins) > 2:
            bad.append('gate %d reads %d wires' % (j, len(ins)))
    for bits, t in spec['rows']:
        if simulate(spec['n'], gates, out, bits) != t:
            bad.append('wrong on input %s (want %d)' % (''.join(map(str, bits)), t))
            break
    return bad


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--gaps')
    ap.add_argument('--id', required=True)
    ap.add_argument('--statement', help='statement text if no gaps file')
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--gates')
    g.add_argument('--record')
    ap.add_argument('--output', type=int)
    ap.add_argument('--out')
    a = ap.parse_args()

    if a.statement:
        gap = {'id': a.id, 'statement': a.statement}
    else:
        gaps = json.load(open(a.gaps, encoding='utf-8'))['gaps']
        gap = next((x for x in gaps if x['id'] == a.id), None)
        if gap is None:
            raise SystemExit('step %s not in %s' % (a.id, a.gaps))
    gap = dict(gap, module='PEqualNP.Outside.' + a.id.replace('-', '_'))
    spec = parse(gap['statement'])
    if spec is None:
        raise SystemExit('statement shape not handled: ' + gap['statement'][:160])

    out = a.output
    if a.record:
        rec = next(r for r in map(json.loads, open(a.record, encoding='utf-8')) if r.get('gates'))
        gates = parse_gates(json.dumps(rec['gates']))
        out = rec.get('output', out)
    else:
        gates = parse_gates(a.gates)
    if out is None:
        out = spec['n'] + len(gates) - 1
    bad = check(spec, gates, out)
    if bad:
        print('REFUSED %s: %s' % (a.id, '; '.join(bad)), file=sys.stderr)
        sys.exit(1)
    text = lean_file(gap, gates, out, spec['general'])
    if a.out:
        with open(a.out, 'w', encoding='utf-8', newline='\n') as f:
            f.write(text)
        print('checked %d gates on %d rows; wrote %s' % (len(gates), len(spec['rows']), a.out), file=sys.stderr)
    else:
        sys.stdout.write(text)


if __name__ == '__main__':
    main()
