"""Compare full synthesis with certificate preflight on complete monotone targets."""
import argparse
import cProfile
from collections import Counter
from dataclasses import asdict
import json
from pathlib import Path
import sys
from time import perf_counter

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[1] / "experiments"), str(HERE.parents[1])]
from certificate_decomposition import complete_status
from ao2_restriction_bounds import direct_reader_caps
from check_prefix_cofactors import checked_prefix_cofactors, load_checked_prefixes
from certificate_rank import analyze, coexistence_color_bound
from certificate_rank_check import gate_count
from certify_synthesis import check_proof
from monotone_frontier import monotone_frontier
from synthesis_bench import direct_sat, peak_bytes
from synthesis_cases import full_rows, truth_table
from synthesis_followup import load_cases
from workflow.supervise import Job, run_jobs


def small_threshold_bound(table):
    """Bounds checked for 2-of-4, 2-of-5, and their AND/OR duals."""
    inputs = len(table).bit_length() - 1
    if inputs not in (4, 5):
        return 0
    for k in (2, inputs - 1):
        if all(high == (row.bit_count() >= k) for row, high in enumerate(table)):
            return 7 if inputs == 4 else 10
    return 0


def evaluate(report, case, budget, preflight, max_excess, proof, lazy, local_intersection,
             preflight_only, conflicts,
             static_coexistence, max_cells, prefix_cofactors, prefix_oracle, closed_sets,
             profile_jsonl, cprofile_path, encode_only, solve_seconds, prefix_evidence,
             port_certificate, port_certificate_output, provider_level, provider_capacity, solver_name):
    start = perf_counter()
    profile_stream = None
    if profile_jsonl:
        profile_path = Path(profile_jsonl)
        profile_path.parent.mkdir(parents=True, exist_ok=True)
        profile_stream = profile_path.open("w", encoding="utf-8")

    def profile_stage(stage, **data):
        if profile_stream is None:
            return
        if stage in ("pattern_encoding_complete", "solver_ready", "solver_iteration"):
            data["peak_process_bytes"] = peak_bytes()
        record = dict(stage=stage, elapsed_seconds=perf_counter() - start, **data)
        profile_stream.write(json.dumps(record, separators=(",", ":")) + "\n")
        profile_stream.flush()
        report("decomposition_profile", phase={"event": stage, **{
            key: value for key, value in data.items() if key in
            ("readers", "iteration", "status", "seconds", "conflicts", "cuts", "clauses")
        }}, profile_stage=stage, **data)

    profile_stage("run_configuration", backend="lazy-certificates" if lazy else "complete-terminal",
                  local_intersection=local_intersection, provider_level=provider_level,
                  provider_level_mode=("shared_static_ancestry" if provider_level and local_intersection
                                       else "model_cuts" if provider_level else None),
                  provider_capacity=provider_capacity, port_certificate=port_certificate,
                  solver=solver_name, per_call_seconds=solve_seconds, conflict_limit=conflicts)
    stage_start = perf_counter()
    if case.known != full_rows(case.n):
        raise ValueError("expected a complete truth table")
    table = [bool(case.truth & (1 << row)) for row in range(1 << case.n)]
    profile_stage("target_table", seconds=perf_counter() - stage_start, rows=len(table), inputs=case.n)
    stage_start = perf_counter()
    positive, negative = monotone_frontier(table)
    if not positive or not negative:
        raise ValueError("expected a nonconstant complete monotone target")
    profile_stage("frontier_extraction", seconds=perf_counter() - stage_start,
                  minterms=len(positive), maximal_false=len(negative))
    stage_start = perf_counter()
    universe = len(table) - 1
    zeros = [universe ^ row for row in negative]
    profile_stage("certificate_conversion", seconds=perf_counter() - stage_start,
                  zero_certificates=len(zeros))
    evidence = {}

    def finish(verdict, method, **result):
        if profile_stream and not profile_stream.closed:
            profile_stream.close()
        return dict(verdict=verdict, method=method, seconds=perf_counter() - start,
                    **evidence, **result)

    if preflight:
        stage_start = perf_counter()
        rank = analyze(positive, zeros)
        floor = rank.gates - rank.excess
        color = floor + coexistence_color_bound(positive, zeros) - 1
        excess = budget - floor
        profile_stage("rank_color_bounds", seconds=perf_counter() - stage_start, rank=rank.rank,
                      rank_gate_bound=rank.gates, color_bound=color, excess=excess)
        evidence.update(rank_bound=rank.gates, color_bound=color, excess=excess,
                        cells=len(positive) * len(zeros))
        if budget < max(rank.gates, color):
            return finish("UNSAT", "rank" if budget < rank.gates else "color")
        if excess <= max_excess:
            report("decomposition", phase={"event": "decomposition", "excess": excess})
            witnesses = []
            traces = []
            stats = Counter()
            prefixes = ()
            if (prefix_cofactors or prefix_oracle) and case.n <= 8 and budget == 2 * case.n - 2:
                checked = {}
                if prefix_oracle:
                    stage_start = perf_counter()
                    if prefix_evidence:
                        prefixes, checked = load_checked_prefixes(prefix_evidence, case.n, case.truth)
                        evidence["cofactor_cache"] = True
                    else:
                        prefixes, checked = checked_prefix_cofactors(case.n, case.truth)
                        evidence["cofactor_cache"] = False
                    evidence["cofactor_checks"] = len(checked["checked"])
                else:
                    stage_start = perf_counter()
                    prefixes = tuple(sum(1 << i for i in fixed)
                                     for fixed, cap in direct_reader_caps(table, budget, case.n - 1,
                                                                         lower_bound=small_threshold_bound)
                                     if cap < 2 * len(fixed))
                profile_stage("cofactor_screen", seconds=perf_counter() - stage_start,
                              exclusions=len(prefixes), recursive_oracle=prefix_oracle,
                              checked_subproblems=len(checked.get("checked", ())),
                              derived_subproblems=len(checked.get("derived", ())))
                evidence["singleton_prefix_exclusions"] = len(prefixes)
                report("cofactor_cuts", phase={"event": "cofactor_cuts", "prefixes": len(prefixes)},
                       prefixes=len(prefixes))

            def witness(_, solution):
                size = gate_count(solution)
                if size > budget or any(solution.evaluate(row) != value for row, value in enumerate(table)):
                    raise RuntimeError("invalid decomposition witness")
                witnesses.append(dict(gates=size, regional=asdict(solution)))

            def verify(readers, variables, clauses, trace):
                steps = check_proof(variables, clauses, [*(trace or ()), "0"])
                traces.append(dict(readers=readers, checked_steps=steps))

            profiler = cProfile.Profile() if cprofile_path else None
            if profiler:
                profiler.enable()
            try:
                status = complete_status(positive, zeros, excess, regions=True, max_cells=max_cells,
                                         conflicts=conflicts, on_sat=witness,
                                         backend="lazy-certificates" if lazy else "complete-terminal",
                                         local_intersection=local_intersection,
                                         static_coexistence=static_coexistence,
                                         singleton_prefix_exclusions=prefixes,
                                         closed_set_cofactors=closed_sets,
                                         portcertrank=port_certificate,
                                         portcertoutput=port_certificate_output,
                                         provider_level=provider_level,
                                         provider_capacity=provider_capacity,
                                         verify_unsat=verify if proof else None, stats=stats,
                                         profile=profile_stage if profile_stream else None,
                                         encode_only=encode_only, solve_seconds=solve_seconds,
                                         solver_name=solver_name)
            finally:
                if profiler:
                    profiler.disable()
                    cprofile_file = Path(cprofile_path)
                    cprofile_file.parent.mkdir(parents=True, exist_ok=True)
                    profiler.dump_stats(str(cprofile_file))
                if profile_stream:
                    profile_stream.close()
            evidence.update(terminal_status=status, terminal_conflicts=stats["conflicts"],
                            terminal_seconds=perf_counter() - start, traces=traces,
                            initial_clauses=stats["initial_clauses"],
                            coexistence_clauses=stats["coexistence_clauses"],
                            singleton_prefix_clauses=stats["singleton_prefix_clauses"],
                            closed_set_clauses=stats["closed_set_clauses"],
                            port_static_clauses=stats["port_static_clauses"],
                            provider_static_clauses=stats["provider_static_clauses"],
                            provider_model_cut_clauses=stats["provider_model_cut_clauses"],
                            provider_model_cut_seconds=stats["provider_model_cut_seconds"],
                            capacity_model_cut_clauses=stats["capacity_model_cut_clauses"],
                            capacity_model_cut_seconds=stats["capacity_model_cut_seconds"],
                            proof_seconds=stats["proof_seconds"],
                            capacity_prefix_layouts=stats["capacity_prefix_layouts"],
                            capacity_prefix_obstructions=sum(value for key, value in stats.items()
                                                             if key.startswith("capacity_prefix_")
                                                             and key.endswith(("_mandatory", "_eligibility", "_primary"))))
            if status == "UNSAT":
                return finish(status, "decomposition")
            if witnesses:
                return finish("SAT", "decomposition", witness=witnesses[0])
        if preflight_only:
            return finish("UNKNOWN", "preflight_limit")

    report("full_synthesis", phase={"event": "full_synthesis"})
    labels = {**dict.fromkeys(positive, True), **dict.fromkeys(negative, False)}
    stats = {}
    stage_start = perf_counter()
    circuit = direct_sat(case.n, labels, budget, False, stats=stats)
    profile_stage("full_synthesis", seconds=perf_counter() - stage_start,
                  verdict="SAT" if circuit is not None else "UNSAT", **stats)
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
    parser.add_argument("--lazy", action="store_true", help="Use lazy certificate search")
    parser.add_argument("--no-local-intersection", action="store_true",
                        help="Keep aggregate intersections and enable lazy model-level cuts")
    parser.add_argument("--static-coexistence", action="store_true",
                        help="Add direct region exclusions for incompatible primary pairs")
    parser.add_argument("--preflight-only", action="store_true", help="Skip full synthesis on an open preflight")
    parser.add_argument("--conflicts", type=int, default=500, help="Requested conflicts per sharing pattern")
    parser.add_argument("--max-cells", type=int, default=400, help="Largest certificate matrix to encode")
    prefixes = parser.add_mutually_exclusive_group()
    prefixes.add_argument("--prefix-cofactors", action="store_true",
                        help="Screen singleton region prefixes with checked small thresholds")
    prefixes.add_argument("--prefix-oracle", action="store_true",
                        help="Check or load a broader collection of small singleton prefix cofactors")
    parser.add_argument("--closed-sets", action="store_true",
                        help="Apply cofactor cuts to all dependency-closed region sets")
    parser.add_argument("--profile-jsonl", help="Write a flushed timing record for each completed stage")
    parser.add_argument("--cprofile", help="Write a Python call profile for the decomposition")
    parser.add_argument("--encode-only", action="store_true",
                        help="Profile formula construction and stop before starting the SAT solver")
    parser.add_argument("--solve-seconds", type=float,
                        help="Interrupt an individual SAT call after this many seconds and retain its statistics")
    parser.add_argument("--prefix-evidence", help="Load checked cofactor evidence for this exact truth table")
    parser.add_argument("--port-certificate", choices=("rank", "clique", "exact"))
    parser.add_argument("--port-certificate-output", action="store_true")
    parser.add_argument("--provider-level", choices=("eligibility", "matching", "exact"))
    parser.add_argument("--provider-capacity", choices=("singletons", "subsets", "exact"))
    parser.add_argument("--solver", choices=("g4", "g42", "glucose42", "cadical195", "maplechrono"),
                        default="g4")
    parser.add_argument("--wall", type=float, default=5)
    args = parser.parse_args()
    cases = load_cases(HERE.parent / "synthesis_cases.json")
    if (args.target not in cases or args.budget < 1 or args.max_excess < 0 or args.max_cells < 1
            or args.solve_seconds is not None and args.solve_seconds <= 0):
        parser.error("expected a corpus target and nonnegative limits")
    if args.solve_seconds is not None and args.solver.startswith("cadical"):
        parser.error("CaDiCaL does not support interruptible solve calls")
    if args.no_local_intersection and not args.lazy:
        parser.error("--no-local-intersection requires --lazy")
    local_intersection = args.lazy and not args.no_local_intersection
    if args.conflicts < 1 or (args.lazy or args.preflight_only or args.proof) and not args.preflight:
        parser.error("preflight options require --preflight and a positive conflict limit")
    if (args.static_coexistence or args.prefix_cofactors or args.prefix_oracle or args.closed_sets) \
            and not local_intersection:
        parser.error("static and cofactor region restrictions require local intersections")
    if args.closed_sets and not (args.prefix_cofactors or args.prefix_oracle):
        parser.error("--closed-sets requires a cofactor screen")
    if args.prefix_evidence and not args.prefix_oracle:
        parser.error("--prefix-evidence requires --prefix-oracle")
    if (args.port_certificate or args.port_certificate_output or args.provider_level
            or args.provider_capacity) and not args.lazy:
        parser.error("port and provider constraints require --lazy")
    if args.port_certificate_output and not args.port_certificate:
        parser.error("--port-certificate-output requires --port-certificate")
    if (args.profile_jsonl or args.cprofile) and not args.preflight:
        parser.error("profiling requires --preflight")
    if args.encode_only and not args.preflight:
        parser.error("--encode-only requires --preflight")
    case = cases[args.target]
    job = Job(case.name, (case, args.budget, args.preflight, args.max_excess, args.proof,
                          args.lazy, local_intersection, args.preflight_only, args.conflicts, args.static_coexistence,
                          args.max_cells, args.prefix_cofactors, args.prefix_oracle, args.closed_sets,
                          args.profile_jsonl, args.cprofile, args.encode_only, args.solve_seconds,
                          args.prefix_evidence, args.port_certificate, args.port_certificate_output,
                          args.provider_level, args.provider_capacity, args.solver),
              dict(budget=args.budget, preflight=args.preflight, max_excess=args.max_excess,
                   proof=args.proof, lazy=args.lazy, local_intersection=local_intersection,
                   conflicts=args.conflicts,
                   static_coexistence=args.static_coexistence, max_cells=args.max_cells,
                   prefix_cofactors=args.prefix_cofactors, prefix_oracle=args.prefix_oracle,
                   closed_sets=args.closed_sets, encode_only=args.encode_only,
                   solve_seconds=args.solve_seconds, prefix_evidence=args.prefix_evidence,
                   port_certificate=args.port_certificate, port_certificate_output=args.port_certificate_output,
                   provider_level=args.provider_level, provider_capacity=args.provider_capacity,
                   solver=args.solver,
                   n=case.n))
    return run_jobs([job], evaluate, workers=1, wall=args.wall, heartbeat=2)


if __name__ == "__main__":
    raise SystemExit(main())
