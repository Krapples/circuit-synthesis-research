"""Compare full synthesis with certificate preflight on complete monotone targets."""
import argparse
from collections import Counter
from dataclasses import asdict
from pathlib import Path
import sys
from time import perf_counter

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[1] / "experiments"), str(HERE.parents[1])]
from certificate_decomposition import complete_status
from certificate_rank import analyze, coexistence_color_bound
from certificate_rank_check import gate_count
from certify_synthesis import check_proof
from monotone_frontier import monotone_frontier
from synthesis_bench import direct_sat
from synthesis_cases import full_rows, truth_table
from synthesis_followup import load_cases
from workflow.supervise import Job, run_jobs


def evaluate(report, case, budget, preflight, max_excess, proof, lazy, preflight_only, conflicts,
             static_coexistence, max_cells):
    start = perf_counter()
    if case.known != full_rows(case.n):
        raise ValueError("expected a complete truth table")
    table = [bool(case.truth & (1 << row)) for row in range(1 << case.n)]
    positive, negative = monotone_frontier(table)
    if not positive or not negative:
        raise ValueError("expected a nonconstant complete monotone target")
    universe = len(table) - 1
    zeros = [universe ^ row for row in negative]
    evidence = {}

    def finish(verdict, method, **result):
        return dict(verdict=verdict, method=method, seconds=perf_counter() - start,
                    **evidence, **result)

    if preflight:
        rank = analyze(positive, zeros)
        floor = rank.gates - rank.excess
        color = floor + coexistence_color_bound(positive, zeros) - 1
        excess = budget - floor
        evidence.update(rank_bound=rank.gates, color_bound=color, excess=excess,
                        cells=len(positive) * len(zeros))
        if budget < max(rank.gates, color):
            return finish("UNSAT", "rank" if budget < rank.gates else "color")
        if excess <= max_excess:
            report("decomposition", phase={"event": "decomposition", "excess": excess})
            witnesses = []
            traces = []
            stats = Counter()

            def witness(_, solution):
                size = gate_count(solution)
                if size > budget or any(solution.evaluate(row) != value for row, value in enumerate(table)):
                    raise RuntimeError("invalid decomposition witness")
                witnesses.append(dict(gates=size, regional=asdict(solution)))

            def verify(readers, variables, clauses, trace):
                steps = check_proof(variables, clauses, [*(trace or ()), "0"])
                traces.append(dict(readers=readers, checked_steps=steps))

            status = complete_status(positive, zeros, excess, regions=True, max_cells=max_cells,
                                     conflicts=conflicts, on_sat=witness,
                                     backend="lazy-certificates" if lazy else "complete-terminal",
                                     local_intersection=lazy,
                                     static_coexistence=static_coexistence,
                                     verify_unsat=verify if proof else None, stats=stats)
            evidence.update(terminal_status=status, terminal_conflicts=stats["conflicts"],
                            terminal_seconds=perf_counter() - start, traces=traces,
                            initial_clauses=stats["initial_clauses"],
                            coexistence_clauses=stats["coexistence_clauses"])
            if status == "UNSAT":
                return finish(status, "decomposition")
            if witnesses:
                return finish("SAT", "decomposition", witness=witnesses[0])
        if preflight_only:
            return finish("UNKNOWN", "preflight_limit")

    report("full_synthesis", phase={"event": "full_synthesis"})
    labels = {**dict.fromkeys(positive, True), **dict.fromkeys(negative, False)}
    stats = {}
    circuit = direct_sat(case.n, labels, budget, False, stats=stats)
    if circuit is None:
        return finish("UNSAT", "full_synthesis", full_stats=stats)
    if len(circuit.gates) > budget or truth_table(case.n, circuit) != case.truth:
        raise RuntimeError("invalid full-synthesis witness")
    return finish("SAT", "full_synthesis", full_stats=stats,
                  witness=dict(gates=len(circuit.gates), circuit=asdict(circuit)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target")
    parser.add_argument("budget", type=int)
    parser.add_argument("--preflight", action="store_true")
    parser.add_argument("--max-excess", type=int, default=6)
    parser.add_argument("--proof", action="store_true")
    parser.add_argument("--lazy", action="store_true", help="Use local-intersection certificate search")
    parser.add_argument("--static-coexistence", action="store_true",
                        help="Add direct region exclusions for incompatible primary pairs")
    parser.add_argument("--preflight-only", action="store_true", help="Skip full synthesis on an open preflight")
    parser.add_argument("--conflicts", type=int, default=500, help="Requested conflicts per sharing pattern")
    parser.add_argument("--max-cells", type=int, default=400, help="Largest certificate matrix to encode")
    parser.add_argument("--wall", type=float, default=5)
    args = parser.parse_args()
    cases = load_cases(HERE.parent / "synthesis_cases.json")
    if args.target not in cases or args.budget < 1 or args.max_excess < 0 or args.max_cells < 1:
        parser.error("expected a corpus target and nonnegative limits")
    if args.conflicts < 1 or (args.lazy or args.preflight_only or args.proof) and not args.preflight:
        parser.error("preflight options require --preflight and a positive conflict limit")
    if args.static_coexistence and not args.lazy:
        parser.error("--static-coexistence requires --lazy")
    case = cases[args.target]
    job = Job(case.name, (case, args.budget, args.preflight, args.max_excess, args.proof,
                          args.lazy, args.preflight_only, args.conflicts, args.static_coexistence,
                          args.max_cells),
              dict(budget=args.budget, preflight=args.preflight, max_excess=args.max_excess,
                   proof=args.proof, lazy=args.lazy, conflicts=args.conflicts,
                   static_coexistence=args.static_coexistence, max_cells=args.max_cells, n=case.n))
    return run_jobs([job], evaluate, workers=1, wall=args.wall, heartbeat=2)


if __name__ == "__main__":
    raise SystemExit(main())
