"""Time-capped, process-isolated ablations for the small synthesis corpus."""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict
import json
from multiprocessing import get_context
import os
from pathlib import Path
import platform
from time import perf_counter, process_time
import traceback

import antichain_search as ac
import cube_search as cs
from monotone_interface import matching_cuts, pinned_interface_excess
from regional_search import MAX_KNOWN_LEAVES
from synthesis_cases import Witness, boundary_labels, corpus, essential, full_rows, trim, truth_table
from pysat.card import CardEnc
from pysat.solvers import Solver


CONFIGS = {
    'A': dict(hitting=False, tight=False, subtreecuts=False),
    'B': dict(hitting=True, tight=False, subtreecuts=False),
    'C': dict(hitting=True, tight=True, subtreecuts=False),
    'D': dict(hitting=True, tight=True, subtreecuts=True),
    'E': dict(hitting=True, tight=True, subtreecuts=True, sharing=1),
}


def direct_sat(n, labels, budget, allow_not):
    """Direct SAT at most budget, with an output selected from any wire."""
    output, pool, clauses, ops, select = cs.build(n, budget, colex_from=budget, require_used=False)
    if not allow_not:
        clauses.extend([-lits[2]] for lits in ops.values())
    outputs = [pool.id(('output', i)) for i in range(output + 1)]
    clauses.extend(CardEnc.equals(outputs, 1, vpool=pool).clauses)
    for row, value in sorted(labels.items()):
        vals = [pool.id(('val', row, j)) for j in range(output + 1)]
        clauses.extend([vals[i] if row >> i & 1 else -vals[i]] for i in range(n))
        clauses.extend(cs.truth_gate_clauses(row, vals, pool, ops, select))
        clauses.extend([-sel, vals[i] if value else -vals[i]] for i, sel in enumerate(outputs))
    with Solver(name='maplechrono', bootstrap_with=clauses) as s:
        if not s.solve():
            return None
        model = set(s.get_model())
    gates = tuple((next(i for i, lit in enumerate(types) if lit in model),
                   next(i for i, lit in enumerate(select[j, 0]) if lit in model),
                   next(i for i, lit in enumerate(select[j, 1]) if lit in model)) for j, types in ops.items())
    return trim(n, Witness(gates, next(i for i, flag in enumerate(outputs) if flag in model)))


def graph_bounds(n, terms):
    cs.REC_CLOSURE[0] = cs.COLOR_BOUNDS[0] = cs.ORDERED[0] = True
    cs.MONO[0] = True
    monotone = cs.port_costs(terms, mono=True, separation=True, profile=True, formula=True, output=True)
    mono = max(cs.rec_lb(terms, 2), cs.port_binary_lb(terms, monotone))
    cuts = matching_cuts(n, terms)
    joint = plain = None
    for right in range(n):
        for left in range(right):
            charge, _ = pinned_interface_excess(n, {0: (0, left, right)}, cuts)
            for op in (0, 1):
                base = cs.cube_binary_lb(terms, (op, left, right), 2, True, monotone)
                plain = base if plain is None else min(plain, base)
                bound = max(n - 1 + charge, base)
                joint = bound if joint is None else min(joint, bound)
    cs.MONO[0] = False
    polarity = cs.port_costs(terms, profile=True, formula=True, polarity=True)
    general = max(cs.rec_lb(terms, 2), cs.port_binary_lb(terms, polarity))
    return dict(ordered_mono=mono, graph_mono_without_matching=max(mono, plain or 0),
                graph_mono=max(mono, joint or 0), graph_not_binary=general)


def analytical(case):
    labels = case.labels()
    boundary = boundary_labels(case.n, labels)
    positive = sum(1 << x for x, high in boundary.items() if high)
    negative = sum(1 << x for x, high in boundary.items() if not high)
    columns = tuple(sum(1 << x for x in boundary if x >> i & 1) for i in range(case.n))
    required = ac.hitting_number(ac.frontier_demands(columns, positive, negative))
    support = max(0, essential(case.n, labels) - 1)
    lower = dict(support=support, frontier=max(0, required - 1), tight=max(0, required - 1))
    if 1 <= required <= MAX_KNOWN_LEAVES:
        if ac.solve_columns(columns, positive, negative, required - 1) is None:
            lower['tight'] = required
    terms = tuple(sorted(x for x, value in boundary.items() if value))
    if case.known == full_rows(case.n) and terms and all(x.bit_count() == 2 for x in terms):
        lower.update(graph_bounds(case.n, terms))
    return lower


def peak_bytes(pid=None):
    system = platform.system()
    if system == 'Windows':
        import ctypes as c
        from ctypes import wintypes as w

        class Counters(c.Structure):
            _fields_ = [('cb', w.DWORD), ('faults', w.DWORD)] + [(name, c.c_size_t) for name in
                        ('peak', 'working', 'peak_paged', 'paged', 'peak_nonpaged', 'nonpaged', 'pagefile', 'peak_pagefile')]

        api = c.WinDLL('kernel32')
        api.OpenProcess.argtypes = (w.DWORD, w.BOOL, w.DWORD)
        api.OpenProcess.restype = w.HANDLE
        api.CloseHandle.argtypes = (w.HANDLE,)
        handle = api.OpenProcess(0x1000, False, pid or os.getpid())
        if not handle:
            return None
        try:
            counters = Counters()
            counters.cb = c.sizeof(counters)
            memory = c.WinDLL('psapi').GetProcessMemoryInfo
            memory.argtypes = (w.HANDLE, c.POINTER(Counters), w.DWORD)
            return counters.peak if memory(handle, c.byref(counters), counters.cb) else None
        finally:
            api.CloseHandle(handle)
    if pid is not None:
        try:
            for line in Path(f'/proc/{pid}/status').read_text().splitlines():
                if line.startswith('VmHWM:'):
                    return int(line.split()[1]) * 1024
        except OSError:
            pass
        return None
    import resource
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return peak if system == 'Darwin' else peak * 1024


def execute(case, config, basis, budget, bounds):
    if config == 'bounds':
        return dict(status='OK', bounds=analytical(case))
    mono = basis == 'mono'
    labels = boundary_labels(case.n, case.labels()) if mono else case.labels()
    stats = Counter()
    rule = 'graph_mono' if config == 'F' else 'graph_not_binary' if config == 'N' else None
    if rule is not None and budget < bounds[rule]:
        return dict(status='UNSAT', source=rule, stats=dict(stats))
    if config in ('SAT', 'N'):
        witness = direct_sat(case.n, labels, budget, not mono)
        source = 'direct SAT'
    else:
        options = CONFIGS['E' if config == 'F' else config]
        solution = ac.solve_partial(case.n, labels, budget, nondegenerate=False, stats=stats, **options)
        witness = None if solution is None else trim(case.n, Witness(solution.gates, solution.output))
        source = 'antichain'
    return dict(status='SAT' if witness is not None else 'UNSAT', witness=witness, stats=dict(stats), source=source)


def worker(pipe, case, config, basis, budget, bounds):
    with pipe:
        pipe.send('ready')
        pipe.recv()
        start = perf_counter()
        cpu = process_time()
        try:
            result = execute(case, config, basis, budget, bounds)
        except Exception:
            result = dict(status='ERROR', error=traceback.format_exc())
        result.update(seconds=perf_counter() - start, cpu_seconds=process_time() - cpu, peak_bytes=peak_bytes())
        pipe.send(result)


def isolated(case, config, basis, budget, bounds, seconds):
    context = get_context('spawn')
    parent, child = context.Pipe()
    process = context.Process(target=worker, args=(child, case, config, basis, budget, bounds))
    process.start()
    child.close()
    try:
        with parent:
            if not parent.poll(20) or parent.recv() != 'ready':
                raise RuntimeError('worker did not start')
            parent.send(True)
            if parent.poll(seconds):
                result = parent.recv()
            else:
                result = dict(status='TIMEOUT', seconds=seconds, peak_bytes=peak_bytes(process.pid))
    finally:
        if process.is_alive():
            process.terminate()
        process.join()
        process.close()
    if result['status'] == 'ERROR':
        raise RuntimeError(result['error'])
    witness = result.get('witness')
    if witness is not None:
        if len(witness.gates) > budget or truth_table(case.n, witness) & case.known != case.truth:
            raise RuntimeError(f'invalid witness for {case.name} {config} {budget}')
        if basis == 'mono' and any(op == 2 for op, _, _ in witness.gates):
            raise RuntimeError('monotone witness used NOT')
        result.update(gates=len(witness.gates), not_gates=sum(op == 2 for op, _, _ in witness.gates),
                      witness=asdict(witness), verified=True)
    return result


def interval(certificates, support, upper):
    lower = support
    for budget, result in certificates:
        if result['status'] == 'SAT':
            upper = min(upper, result['gates'])
        elif result['status'] == 'UNSAT':
            lower = max(lower, budget + 1)
    if lower > upper:
        raise RuntimeError(f'inconsistent interval [{lower}, {upper}]')
    return dict(lower=lower, upper=upper, minimum=lower if lower == upper else None)


COVER_SEED = [True]  # --no-cover-seed reproduces runs recorded before 2026-11-25


def cover_seed(case):
    """Verified star-cover circuit (L-meta-154) for complete graph edge functions, else None."""
    terms = tuple(sorted(x for x, value in case.labels().items() if value))
    if case.known != full_rows(case.n) or not terms:
        return None
    minimal = [x for x in terms if not any(y != x and y & x == y for y in terms)]
    if not all(x.bit_count() == 2 for x in minimal):
        return None
    if any(any(row & x == x for x in minimal) != value for row, value in case.labels().items()):
        return None  # not the monotone function generated by these edges
    edges = [tuple(i for i in range(case.n) if x >> i & 1) for x in minimal]
    gates = cs.cover_circuit(case.n, edges)
    witness = Witness(tuple(gates), case.n + len(gates) - 1)
    if truth_table(case.n, witness) != case.truth:
        raise RuntimeError(f'invalid star-cover witness for {case.name}')
    return witness


def run_case(case, seconds, probes, record):
    support = max(0, essential(case.n, case.labels()) - 1)
    upper = len(case.witness.gates)
    if truth_table(case.n, case.witness) & case.known != case.truth:
        raise RuntimeError(f'invalid corpus witness for {case.name}')
    cover = cover_seed(case) if COVER_SEED[0] else None
    if cover is not None and len(cover.gates) < upper:
        upper = len(cover.gates)
        record(dict(kind='seed', case=case.name, family=case.family, n=case.n, rule='L-meta-154 star cover',
                    gates=upper, corpus_gates=len(case.witness.gates), witness=asdict(cover), verified=True))
    computed = isolated(case, 'bounds', None, None, {}, seconds)
    bounds = computed.pop('bounds', dict(support=support))
    record(dict(kind='analytical', case=case.name, family=case.family, n=case.n, bounds=bounds, **computed))
    for basis in ('mono', 'not'):
        reference, outcomes = {}, []
        graph_rule = 'graph_mono' if basis == 'mono' else 'graph_not_binary'

        def run(config, budget, phase):
            result = isolated(case, config, basis, budget, bounds, seconds)
            record(dict(kind='job', case=case.name, family=case.family, n=case.n, basis=basis,
                        configuration=config, phase=phase, budget=budget, **result))
            outcomes.append((budget, result))
            return result

        for _ in range(probes):
            limits = interval(reference.items(), support, upper)
            possible = [b for b in range(limits['lower'], limits['upper']) if b not in reference]
            if not possible:
                break
            middle = (limits['lower'] + limits['upper'] - 1) // 2
            budget = min(possible, key=lambda b: (abs(b - middle), b))
            reference[budget] = run('SAT', budget, 'reference')
        limits = interval(reference.items(), support, upper)
        budgets = {limits['lower'] - 1, limits['upper']}
        if limits['minimum'] is None:
            # Probe just below an analytical claim when it can improve the reference.
            analytic = max(bounds.get('tight', support), bounds.get(graph_rule, support)) if basis == 'mono' else bounds.get(graph_rule, support)
            budgets.add(min(limits['upper'], max(limits['lower'] + 1, analytic)) - 1)
        configs = (['SAT', *CONFIGS, *(['F'] if graph_rule in bounds else [])] if basis == 'mono'
                   else ['SAT', *(['N'] if graph_rule in bounds else [])])
        for b in sorted(budgets - {-1}):
            for config in configs:
                if config == 'SAT' and b in reference:
                    continue  # reuse the recorded SAT measurement at this budget
                run(config, b, 'ablation')
        final = interval(outcomes, support, upper)
        record(dict(kind='interval', case=case.name, family=case.family, n=case.n, basis=basis,
                    budgets=sorted(budgets - {-1}), applicable=configs, reference=limits, final=final,
                    initial_upper=upper))
        upper = final['upper']  # the monotone witness is also an upper bound with NOT allowed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--manifest', type=Path, help='write the deterministic 100-case corpus as JSON')
    parser.add_argument('--family', action='append', default=[])
    parser.add_argument('--case', action='append', default=[])
    parser.add_argument('--per-family', type=int, help='cap each selected family, preserving corpus order')
    parser.add_argument('--seconds', type=float, default=1.0, help='fixed solver wall-time cap per job')
    parser.add_argument('--probes', type=int, default=3, help='maximum reference SAT probes per basis and case')
    parser.add_argument('--workers', type=int, default=1, help='concurrent cases (use one for serial timings)')
    parser.add_argument('--no-cover-seed', action='store_true',
                        help='start from the corpus witness only (reproduces runs before 2026-11-25)')
    args = parser.parse_args()
    COVER_SEED[0] = not args.no_cover_seed
    if not args.manifest and not args.output:
        parser.error('provide --manifest, --output, or both')
    if not args.seconds > 0 or args.probes < 0 or args.workers < 1 or args.per_family is not None and args.per_family < 1:
        parser.error('time must be positive and probe and case limits must be valid')
    cases = corpus()
    if args.manifest:
        with args.manifest.open('x', encoding='utf-8') as output:
            json.dump([asdict(case) for case in cases], output, indent=2)
            output.write('\n')
    if not args.output:
        return
    selected, counts = [], Counter()
    for case in cases:
        if (args.family and case.family not in args.family or args.case and case.name not in args.case
                or args.per_family is not None and counts[case.family] >= args.per_family):
            continue
        counts[case.family] += 1
        selected.append(case)
    if not selected:
        parser.error('no cases match the selection')
    with args.output.open('x', encoding='utf-8') as output:
        def write(row):
            output.write(json.dumps(row, sort_keys=True) + '\n')
            output.flush()

        write(dict(kind='meta', schema=1, seconds=args.seconds, probes=args.probes, workers=args.workers,
                   cases=[c.name for c in selected],
                   python=platform.python_version(), os=platform.platform(), solver='maplechrono'))
        if args.workers == 1:
            for i, case in enumerate(selected, 1):
                print(f'[{i}/{len(selected)}] {case.name}', flush=True)
                run_case(case, args.seconds, args.probes, write)
        else:
            def batch(case):
                rows = []
                run_case(case, args.seconds, args.probes, rows.append)
                return rows

            with ThreadPoolExecutor(max_workers=args.workers) as executor:
                for i, (case, rows) in enumerate(zip(selected, executor.map(batch, selected)), 1):
                    for row in rows:
                        write(row)
                    print(f'[{i}/{len(selected)}] {case.name}', flush=True)


if __name__ == '__main__':
    main()
