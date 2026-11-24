"""Independently encode monotone synthesis and check an UNSAT proof by unit propagation."""

import argparse
from collections import defaultdict
import gzip
import json
from pathlib import Path
from time import perf_counter

from synthesis_cases import boundary_labels
from synthesis_followup import digest, load_cases
from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver


def encode(n, labels, budget):
    """Independent pair-selection encoding, with final identity gates for padding."""
    pool = IDPool()
    clauses = []
    readers = defaultdict(list)
    choices = {}
    buffers = []
    for j in range(n, n + budget):
        rows = [(op, left, right) for right in range(j) for left in range(right) for op in (0, 1)]
        rows += [(1, i, i) for i in (range(n) if j == n else (j - 1,))]
        buffer = pool.id(('buffer', j))
        buffers.append(buffer)
        picks = []
        for recipe in rows:
            op, a, b = recipe
            pick = pool.id(('gate', j, recipe))
            readers[a].append(pick)
            if b != a:
                readers[b].append(pick)
            picks.append((pick, op, a, b))
            clauses.append([-pick, buffer if a == b else -buffer])
        choices[j] = picks
        clauses.extend(CardEnc.equals([p for p, *_ in picks], 1, vpool=pool).clauses)
    clauses.extend([-a, b] for a, b in zip(buffers, buffers[1:]))
    for j in range(n, n + budget - 1):
        clauses.append(readers[j])
    # Pick a topological order of real gates by the largest already assigned operand.
    # An identity following the last real gate already has the largest possible operand.
    for j in range(n, n + budget - 1):
        for p, _, _, right in choices[j]:
            clauses.extend([-p, -q] for q, _, _, other in choices[j + 1] if other < right)

    output = n + budget - 1
    for row, target in sorted(labels.items()):
        wires = [pool.id(('value', j, row)) for j in range(n + budget)]
        clauses.extend([wires[i] if row >> i & 1 else -wires[i]] for i in range(n))
        clauses.append([wires[output] if target else -wires[output]])
        for j, picks in choices.items():
            z = wires[j]
            for pick, op, a, b in picks:
                x, y = wires[a], wires[b]
                if op == 0:
                    clauses.extend(([-pick, -x, -y, z], [-pick, x, -z], [-pick, y, -z]))
                else:
                    clauses.extend(([-pick, x, y, -z], [-pick, -x, z], [-pick, -y, z]))
    return pool.top, clauses


class RupChecker:
    """Check that each added clause follows by reverse unit propagation."""

    def __init__(self, variables, clauses):
        self.variables = variables
        self.units = []
        self.watched = defaultdict(list)
        self.empty = False
        for clause in clauses:
            self.add(clause)

    def add(self, literals):
        clause = list(dict.fromkeys(literals))
        if not clause:
            self.empty = True
        elif len(clause) == 1:
            self.units.append(clause[0])
        else:
            self.watched[clause[0]].append(clause)
            self.watched[clause[1]].append(clause)

    def contradicts(self, assumptions):
        if self.empty:
            return True
        values = [0] * (self.variables + 1)
        trail = []

        def assign(lit):
            i, sign = abs(lit), 1 if lit > 0 else -1
            if values[i] == -sign:
                return False
            if not values[i]:
                values[i] = sign
                trail.append(lit)
            return True

        def value(lit):
            return values[lit] if lit > 0 else -values[-lit]

        if not all(assign(lit) for lit in (*self.units, *assumptions)):
            return True
        for lit in trail:
            dead = -lit
            watches = self.watched[dead]
            i = 0
            while i < len(watches):
                clause = watches[i]
                if clause[0] == dead:
                    clause[0], clause[1] = clause[1], clause[0]
                other = clause[0]
                if value(other) > 0:
                    i += 1
                    continue
                for k in range(2, len(clause)):
                    if value(clause[k]) >= 0:
                        clause[1], clause[k] = clause[k], clause[1]
                        self.watched[clause[1]].append(clause)
                        watches[i] = watches[-1]
                        watches.pop()
                        break
                else:
                    if not assign(other):
                        return True
                    i += 1
        return False


def check_proof(variables, clauses, proof):
    checker = RupChecker(variables, clauses)
    steps = 0
    for line in proof:
        fields = line.split()
        if not fields or fields[0] == 'd':
            continue  # retaining clauses only strengthens reverse unit propagation
        numbers = list(map(int, fields))
        if numbers[-1] != 0 or any(not lit or abs(lit) > variables for lit in numbers[:-1]):
            raise ValueError(f'invalid proof line {steps + 1}')
        clause = numbers[:-1]
        if not checker.contradicts(-lit for lit in clause):
            raise ValueError(f'proof step {steps + 1} failed reverse unit propagation')
        checker.add(clause)
        steps += 1
        if not clause:
            return steps
    raise ValueError('proof did not derive the empty clause')


def write_gzip(path, lines):
    with path.open('xb') as stream, gzip.GzipFile(filename='', mode='wb', fileobj=stream, mtime=0) as zipped:
        for line in lines:
            zipped.write((line + '\n').encode('ascii'))


def read_cnf(cnf):
    with gzip.open(cnf, 'rt', encoding='ascii') as f:
        prefix, format_, variables, count = f.readline().split()
        variables, count = int(variables), int(count)
        if prefix != 'p' or format_ != 'cnf' or variables < 0 or count < 0:
            raise ValueError('invalid CNF header')
        clauses = []
        for line in f:
            numbers = list(map(int, line.split()))
            if not numbers or numbers[-1] or any(not lit or abs(lit) > variables for lit in numbers[:-1]):
                raise ValueError('invalid CNF clause')
            clauses.append(numbers[:-1])
    if len(clauses) != count:
        raise ValueError('wrong number of clauses')
    return variables, clauses


def verify_files(cnf, proof):
    variables, clauses = read_cnf(cnf)
    with gzip.open(proof, 'rt', encoding='ascii') as f:
        return check_proof(variables, clauses, f)


def verify_encoding(metadata, manifest):
    """Bind a saved proof to its declared target and independently rebuild the CNF."""
    record = json.loads(metadata.read_text(encoding='utf-8'))
    if record['basis'] != 'mono' or digest(manifest) != record['target_manifest_sha256']:
        raise ValueError('mismatched target manifest or basis')
    paths = tuple(metadata.parent / name for name in record['files'])
    if any(digest(path) != record['files'][path.name] for path in paths):
        raise ValueError('certificate hash mismatch')
    cnf = next(path for path in paths if path.name.endswith('.cnf.gz'))
    proof = next(path for path in paths if path.name.endswith('.drup.gz'))
    case = load_cases(manifest)[record['case']]
    rebuilt = encode(case.n, boundary_labels(case.n, case.labels()), record['budget'])
    if rebuilt != read_cnf(cnf) or (rebuilt[0], len(rebuilt[1])) != (record['variables'], record['clauses']):
        raise ValueError('saved CNF does not match the target and budget')
    return cnf, proof


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--case')
    parser.add_argument('--budget', type=int)
    parser.add_argument('--output', type=Path, help='new file prefix for the CNF, proof, and metadata')
    parser.add_argument('--conflicts', type=int, default=100000)
    parser.add_argument('--verify', nargs=2, type=Path, metavar=('CNF', 'PROOF'))
    parser.add_argument('--verify-packet', type=Path, help='bind metadata to its manifest and check the proof')
    args = parser.parse_args()
    if args.verify:
        print(f'Verified {verify_files(*args.verify)} reverse unit propagation steps')
        return
    if args.verify_packet:
        if not args.manifest:
            parser.error('--verify-packet requires the target manifest')
        cnf, proof = verify_encoding(args.verify_packet, args.manifest)
        print(f'Verified target, encoding, and {verify_files(cnf, proof)} reverse unit propagation steps')
        return
    if not args.manifest or not args.case or args.budget is None or args.budget < 1 or not args.output:
        parser.error('provide a manifest, case, positive budget, and output prefix')
    case = load_cases(args.manifest)[args.case]
    labels = boundary_labels(case.n, case.labels())
    variables, clauses = encode(case.n, labels, args.budget)
    start = perf_counter()
    with Solver(name='glucose4', bootstrap_with=clauses, with_proof=True) as solver:
        solver.conf_budget(args.conflicts)
        verdict = solver.solve_limited()
        if verdict is not False:
            raise SystemExit('SAT' if verdict else 'INCONCLUSIVE at the conflict limit')
        proof = solver.get_proof()
    solving = perf_counter() - start
    # Some solvers leave the final empty clause implicit in the returned trace.
    checked = perf_counter()
    if not any(line.strip() == '0' for line in proof):
        proof.append('0')
    steps = check_proof(variables, clauses, proof)
    checking = perf_counter() - checked
    cnf_path = args.output.with_suffix('.cnf.gz')
    proof_path = args.output.with_suffix('.drup.gz')
    write_gzip(cnf_path, (f'p cnf {variables} {len(clauses)}', *(' '.join(map(str, (*c, 0))) for c in clauses)))
    write_gzip(proof_path, proof)
    record = dict(case=case.name, budget=args.budget, basis='mono', variables=variables, clauses=len(clauses),
                  checked_steps=steps, solve_seconds=solving, check_seconds=checking, target_manifest_sha256=digest(args.manifest),
                  files={p.name: digest(p) for p in (cnf_path, proof_path)})
    with args.output.with_suffix('.json').open('x', encoding='utf-8') as f:
        json.dump(record, f, indent=2)
        f.write('\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
