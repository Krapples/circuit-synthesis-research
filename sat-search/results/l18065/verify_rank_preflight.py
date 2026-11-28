"""Replay the L18065 rank screen and check the decisive decomposition traces."""
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "experiments"))
from ao2_restriction_bounds import frontier_rank_bound
from certificate_decomposition import complete_status
from certify_synthesis import check_proof
from l18065_sweep import graphs
from l18065_synth import fval, simulate
from monotone_frontier import monotone_frontier


def star_witness(m, edges):
    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return 2 * m + len(gates) - 1

    def collect(wires):
        wire, *rest = wires
        for other in rest:
            wire = gate(0, wire, other)
        return wire

    stars = [gate(1, a, collect([m + b for x, b in edges if x == a])) for a in range(m)]
    collect(stars)
    return gates


def main():
    cases = sorted((graph for m in (3, 4) for graph in graphs(m)),
                   key=lambda graph: (graph[0], len(graph[1])))
    for case, (m, edges) in enumerate(cases):
        truth = [fval(m, edges, row) for row in range(1 << (2 * m))]
        positive, negative = monotone_frontier(truth)
        bound = frontier_rank_bound(positive, negative, len(truth) - 1)
        gates = star_witness(m, edges)
        for row, value in enumerate(truth):
            wires = simulate(2 * m, gates, row)
            assert wires[-1] == value
            assert value or all(not wires[2 * m + i] for i, (op, _, _) in enumerate(gates) if op)
        budget = len(gates) - 1
        result = dict(case=case, m=m, edges=edges, rank=bound.rank, rank_gate_bound=bound.gates,
                      excluded_budget=budget, minimum=len(gates))
        if budget < bound.gates:
            assert bound.gates == len(gates)
            result["method"] = "certificate_rank"
        else:
            checked = []

            def verify(readers, variables, clauses, trace):
                steps = check_proof(variables, clauses, [*(trace or ()), "0"])
                checked.append(dict(readers=readers, variables=variables, clauses=len(clauses),
                                    checked_steps=steps))

            zeros = [(len(truth) - 1) ^ row for row in negative]
            excess = budget - (bound.gates - bound.excess)
            assert complete_status(positive, zeros, excess, regions=True, conflicts=500,
                                   verify_unsat=verify) == "UNSAT"
            assert checked
            result.update(method="certificate_decomposition", excess=excess, trace_checks=checked)
        print(json.dumps(result, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
