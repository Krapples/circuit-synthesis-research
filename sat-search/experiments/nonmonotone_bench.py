"""A separate AND/OR/NOT synthesis corpus with nonmonotonicity certificates."""

import argparse
from dataclasses import asdict
import json
from pathlib import Path

from synthesis_bench import interval, isolated
from synthesis_cases import Builder, Case, essential, full_rows, threshold, truth_table


class SignedBuilder(Builder):
    def negate(self, wire):
        op = (2, wire, wire)
        if op not in self.memo:
            self.memo[op] = self.n + len(self.gates)
            self.gates.append(op)
        return self.memo[op]

    def xor(self, a, b):
        return self.gate(0, self.gate(1, a, b), self.negate(self.gate(0, a, b)))

    def mux(self, select, high, low):
        return self.gate(1, self.gate(0, select, high), self.gate(0, self.negate(select), low))

    def inline(self, witness):
        wires = list(range(self.n))
        for op, a, b in witness.gates:
            wires.append(self.gate(op, wires[a], wires[b]))
        return wires[witness.output]


def descending_edge(case):
    for low, high in case.labels().items():
        if high:
            for bit in range(case.n):
                if not low >> bit & 1:
                    above = low | (1 << bit)
                    if not case.truth >> above & 1:
                        return low, above
    return None


def signed_cases():
    cases = []

    def add(name, family, builder, output):
        witness = builder.finish(output)
        n = builder.n
        case = Case(name, family, n, full_rows(n), truth_table(n, witness), witness)
        if descending_edge(case) is None or essential(n, case.labels()) != n:
            raise ValueError(f'invalid nonmonotone case {name}')
        cases.append(case)

    for n in range(2, 6):
        b = SignedBuilder(n)
        out = 0
        for i in range(1, n):
            out = b.xor(out, i)
        add(f'parity-{n}', 'parity', b, out)
    b = SignedBuilder(3)
    add('mux-2-to-1', 'mux', b, b.mux(0, 1, 2))
    b = SignedBuilder(4)
    add('mux-or', 'mux', b, b.mux(0, 1, b.gate(1, 2, 3)))
    b = SignedBuilder(5)
    add('mux-and-or', 'mux', b, b.mux(0, b.gate(0, 1, 2), b.gate(1, 3, 4)))
    b = SignedBuilder(6)
    add('mux-4-to-1', 'mux', b, b.mux(0, b.mux(1, 2, 3), b.mux(1, 4, 5)))
    for n, k in ((3, 1), (4, 2), (5, 2), (6, 3)):
        b = SignedBuilder(n)
        low, high = b.inline(threshold(n, k)), b.inline(threshold(n, k + 1))
        add(f'exactly-{k}-of-{n}', 'exactly', b, b.gate(0, low, b.negate(high)))
    b = SignedBuilder(2)
    add('nand-2', 'negative-control', b, b.negate(b.gate(0, 0, 1)))
    b = SignedBuilder(2)
    add('inhibit-2', 'negative-control', b, b.gate(0, 0, b.negate(1)))
    b = SignedBuilder(4)
    add('mixed-conjunction-4', 'negative-control', b, b.fold(0, (0, 1, 2, b.negate(3))))
    b = SignedBuilder(5)
    add('signed-branches-5', 'negative-control', b,
        b.gate(1, b.fold(0, (0, 1, b.negate(2))), b.gate(0, b.negate(3), 4)))
    return cases


def run_case(case, seconds, probes, write):
    support = case.n  # n-1 binary gates for connectivity, and at least one NOT
    upper = len(case.witness.gates)
    tried = {}

    def run(budget):
        result = isolated(case, 'SAT', 'not', budget, {}, seconds)
        tried[budget] = result
        write(dict(kind='job', case=case.name, family=case.family, basis='not', budget=budget, **result))

    for _ in range(probes):
        limits = interval(tried.items(), support, upper)
        lower, ceiling = limits['lower'], limits['upper']
        options = [b for b in range(lower, ceiling) if b not in tried]
        if not options:
            break
        budget = lower if lower in options else min(options, key=lambda b: abs(b - (lower + ceiling) // 2))
        run(budget)
    limits = interval(tried.items(), support, upper)
    # Measure both sides of the best bracket, even when a construction or lower bound supplied it.
    for budget in (limits['lower'] - 1, limits['upper']):
        if budget not in tried:
            run(budget)
    result = interval(tried.items(), support, upper)
    write(dict(kind='interval', case=case.name, family=case.family, n=case.n, basis='not',
               monotone_obstruction=descending_edge(case), final=result))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=1.0)
    parser.add_argument('--probes', type=int, default=4)
    args = parser.parse_args()
    if not args.seconds > 0 or args.probes < 0:
        parser.error('invalid time or probe limit')
    cases = signed_cases()
    with args.manifest.open('x', encoding='utf-8') as manifest:
        json.dump([asdict(c) for c in cases], manifest, indent=2)
        manifest.write('\n')
    with args.output.open('x', encoding='utf-8') as output:
        def write(row):
            output.write(json.dumps(row, sort_keys=True) + '\n')
            output.flush()

        write(dict(kind='meta', seconds=args.seconds, probes=args.probes, cases=[c.name for c in cases]))
        for case in cases:
            result = run_case(case, args.seconds, args.probes, write)
            print(case.name, result, flush=True)


if __name__ == '__main__':
    main()
