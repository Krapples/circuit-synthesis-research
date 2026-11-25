"""Check the native slack-three boundary recognizer against an independent DAG enumeration.

The exact answer (residual_slack_two::Engine at slack three) is compared with a canonical
breadth-first enumeration of trimmed distinct-fanin free-NOT AIGs with exactly k + 2 gates.
Retained extensions are replayed in the recognizer's order with the same enumeration standing in
for each lower-slack recognizer, so the retained union and the feasible/excluded/subsumed counts
are checked without using native code. ``--capture`` replays boundaries traced by
``percy_run --trace-slack-three`` with both tree backends and every requested mode.
"""

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import sys
from time import perf_counter
from types import SimpleNamespace

from slack_one_native_check import _native, captured_boundaries

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'baselines'))
from benchmark_memory import limit_commit_mib


def independent_columns(n):
    return tuple(sum(1 << row for row in range(1 << n) if row >> i & 1) for i in range(n))


def types(primaries):
    return [column for b, y in enumerate(primaries) for x in primaries[:b]
            for column in (x & ~y, ~x & y, x & y, x | y)]


def verify(columns, h, target, care, regions, slack=3):
    """Check a returned witness: exact gate count, read counts, raw pairs and the output."""
    anchor = care & -care

    def normalize(col):
        return (col & care) ^ (care if col & anchor else 0)

    wires = {i: (normalize(col), i >= h) for i, col in enumerate(columns)}
    reads = Counter()
    gates = 0
    assert 1 <= len(regions) <= slack + 1
    for out, col, inputs, (tree, phase) in regions:
        assert out == len(wires)
        assert len(inputs) >= 2
        occurrences = Counter()

        def evaluate(node):
            nonlocal gates
            if node[0] == 'x':
                occurrence = node[1]
                assert 0 <= occurrence < len(inputs)
                wire, value, raw = inputs[occurrence]
                assert wires[wire] == (value, raw)
                occurrences[occurrence] += 1
                reads[wire] += 1
                return value
            op, pa, pb, po, a, b = node
            assert op == '&'
            if a[0] == b[0] == 'x':
                left, right = inputs[a[1]], inputs[b[1]]
                assert left[0] != right[0] and not (left[2] and right[2])
            gates += 1
            return ((evaluate(a) ^ (care if pa else 0)) &
                    (evaluate(b) ^ (care if pb else 0))) ^ (care if po else 0)

        assert evaluate(tree) ^ (care if phase else 0) == col & care
        assert occurrences == dict.fromkeys(range(len(inputs)), 1)
        wires[out] = col, False
    assert (col ^ target) & care == 0
    assert set(reads) == set(wires) - {out}
    assert all(reads[wire] >= 2 for wire in range(len(columns), out))
    assert sum(count - 1 for count in reads.values()) == slack
    assert gates == len(columns) - 1 + slack


def dag_tables(columns, h, care, gates):
    """Output tables of trimmed distinct-fanin DAGs with exactly ``gates`` gates over the leaves.

    Leaves at index >= h are raw primaries and may not feed the same gate. States are canonical:
    the leaves' read bits plus the sorted multiset of (gate column, read) pairs. A trimmed DAG has
    one sink, so it has a topological order ending in the only unread gate.
    """
    k = len(columns)
    columns = [col & care for col in columns]
    states = {(0, ())}
    for left in range(gates, 0, -1):
        following = set()
        for leaf_reads, gate_wires in states:
            wires = [*columns, *(col for col, _ in gate_wires)]
            reads = [leaf_reads >> i & 1 for i in range(k)] + [read for _, read in gate_wires]
            for a, b in combinations(range(len(wires)), 2):
                if h <= a < b < k:
                    continue
                new_reads = list(reads)
                new_reads[a] = new_reads[b] = 1
                unread = new_reads.count(0) + 1
                if unread - (left - 1) > 1:
                    continue
                x, y = wires[a], wires[b]
                leaf_bits = sum(new_reads[i] << i for i in range(k))
                pairs = [(wires[i], new_reads[i]) for i in range(k, len(wires))]
                for value in (x & ~y, ~x & y, x & y, x | y):
                    following.add((leaf_bits, tuple(sorted([*pairs, (value & care, 0)]))))
        states = following
    tables = set()
    full_leaves = (1 << k) - 1
    for leaf_reads, gate_wires in states:
        unread = [col for col, read in gate_wires if not read]
        if leaf_reads == full_leaves and len(unread) == 1:
            tables.update((unread[0], unread[0] ^ care))
    return tables


def feasible(columns, h, target, care, slack):
    return target & care in dag_tables(columns, h, care, len(columns) - 1 + slack)


def expected_extensions(columns, h, primaries, mixed, gate_columns, target, care):
    """Replay the recognizer's extension order with the independent enumeration."""
    free = [i for i in range(len(primaries)) if not mixed >> i & 1]
    kept_mixed = kept_gates = 0
    counts = Counter()

    def visit(bits, gate_bits, wires, first, slack):
        nonlocal kept_mixed, kept_gates
        if kept_mixed & bits == bits and kept_gates & gate_bits == gate_bits:
            counts['subsumed'] += 1
            return
        if feasible(wires, first, target, care, slack):
            counts['feasible'] += 1
            kept_mixed |= bits
            kept_gates |= gate_bits
        else:
            counts['excluded'] += 1

    def with_gate(gate):
        return [*columns[:h], gate_columns[gate], *columns[h:]]

    for a, b, c in combinations(free, 3):
        visit(1 << a | 1 << b | 1 << c, 0, [*columns, primaries[a], primaries[b], primaries[c]], h, 0)
    for gate in range(len(gate_columns)):
        for i in free:
            visit(1 << i, 1 << gate, [*with_gate(gate), primaries[i]], h + 1, 0)
    for a, b in combinations(free, 2):
        visit(1 << a | 1 << b, 0, [*columns, primaries[a], primaries[b]], h, 1)
    for gate in range(len(gate_columns)):
        visit(0, 1 << gate, with_gate(gate), h + 1, 1)
    for i in free:
        visit(1 << i, 0, [*columns, primaries[i]], h, 2)
    return kept_mixed, kept_gates, counts


def all_extensions(columns, h, primaries, mixed, gate_columns):
    """Every extension of cost <= 3 as (cost, mixed bits, gate bits, wires, first, exact slack)."""
    free = [i for i in range(len(primaries)) if not mixed >> i & 1]

    def with_gate(gate):
        return [*columns[:h], gate_columns[gate], *columns[h:]]

    out = [(1, 1 << i, 0, [*columns, primaries[i]], h, 2) for i in free]
    out += [(2, 1 << a | 1 << b, 0, [*columns, primaries[a], primaries[b]], h, 1) for a, b in combinations(free, 2)]
    out += [(2, 0, 1 << gate, with_gate(gate), h + 1, 1) for gate in range(len(gate_columns))]
    out += [(3, 1 << a | 1 << b | 1 << c, 0, [*columns, primaries[a], primaries[b], primaries[c]], h, 0)
            for a, b, c in combinations(free, 3)]
    out += [(3, 1 << i, 1 << gate, [*with_gate(gate), primaries[i]], h + 1, 0)
            for gate in range(len(gate_columns)) for i in free]
    return out


def lazy_sound(metrics, extensions, oracle):
    """NOT A OR (W >= w + d) OR R: every feasible extension cheaper than d meets R."""
    d, kept_mixed, kept_gates = metrics['lift'], metrics['mixed_extensions'], metrics['gate_extensions']
    assert 1 <= d <= 4, metrics
    for (cost, bits, gate_bits, *_), ok in zip(extensions, oracle):
        if ok and cost < d:
            assert bits & kept_mixed or gate_bits & kept_gates, (cost, bits, gate_bits, metrics)
    # Retained elements come only from feasible (or unknown) extensions.
    if metrics['extension_unknown'] == 0:
        elements_mixed = elements_gates = 0
        for (cost, bits, gate_bits, *_), ok in zip(extensions, oracle):
            if ok:
                elements_mixed |= bits
                elements_gates |= gate_bits
        assert kept_mixed & ~elements_mixed == 0 and kept_gates & ~elements_gates == 0, metrics


def check_policies():
    """Exact-only, cost-one lift and adaptive policies against the independent enumeration."""
    a, b, c, d, e = primaries = independent_columns(5)
    care = 0xffffffff
    gate_columns = types(primaries)
    columns, h, mixed = [a & b, c], 1, 4
    extensions = all_extensions(columns, h, primaries, mixed, gate_columns)
    counts = Counter()
    for target in (a & b & c & d & e, (a & b & c) ^ d, (a & b) | (c & d & e), (a & b & c) ^ (d & e)):
        oracle = [feasible(wires, first, target, care, slack) for _, _, _, wires, first, slack in extensions]

        def call(policy, memo=None, deadline=0):
            return _native.slack_three_boundary(columns, h, primaries, mixed, gate_columns, target, care,
                                                2_000_000, deadline, 5, True, policy, memo)

        for policy in (0, 1, 2, 3):
            metrics, regions = call(policy)
            assert metrics['status'] == 0 and not regions, metrics
            lazy_sound(metrics, extensions, oracle)
            assert metrics['extension_total'] == len(extensions), metrics
            counts[f'policy{policy}'] += 1
        exact, _ = call(1)
        assert exact['lift'] == 1 and not exact['mixed_extensions'] and not exact['gate_extensions'], exact
        assert exact['tight_calls'] == exact['slack_one_calls'] == exact['slack_two_calls'] == 0, exact
        lift1, _ = call(2)
        singles = sum(bits for (cost, bits, *_), ok in zip(extensions, oracle) if cost == 1 and ok)
        assert lift1['lift'] == 2 and lift1['mixed_extensions'] == singles and not lift1['gate_extensions'], lift1
        assert lift1['slack_two_calls'] == sum(cost == 1 for cost, *_ in extensions), lift1
        adaptive, _ = call(3)
        assert adaptive['lift'] == 4 and adaptive['extension_unknown'] == 0, adaptive
        counts['adaptive_covered'] += adaptive['covered']
        # A shared memo answers the repeated query without recomputation.
        memo = _native.ResidualMemo()
        first_run, _ = call(3, memo)
        again, _ = call(3, memo)
        assert again['exact_cached'] and again['memo_hits'] > 0 and again['memo_inserts'] == 0, again
        assert again['tight_calls'] == again['slack_one_calls'] == again['slack_two_calls'] == 0, again
        assert (again['mixed_extensions'], again['gate_extensions'], again['lift']) == (
            first_run['mixed_extensions'], first_run['gate_extensions'], first_run['lift'])
        lazy_sound(again, extensions, oracle)
        counts['memo_repeat'] += 1
        # Past the deadline only memo answers are decided: the first untested level sets d.
        for seeded_levels, expected_lift in ((0, 1), (1, 2)):
            memo = _native.ResidualMemo()
            memo.insert(target, care, columns, h, 3, False)
            for (cost, bits, gate_bits, wires, first, slack), ok in zip(extensions, oracle):
                if cost <= seeded_levels:
                    memo.insert(target, care, wires, first, slack, ok)
            metrics, _ = call(3, memo, 1e-12)
            assert metrics['status'] == 0 and metrics['exact_cached'], metrics
            assert metrics['lift'] == expected_lift, (seeded_levels, metrics)
            lazy_sound(metrics, extensions, oracle)
            if expected_lift == 1:
                assert not metrics['mixed_extensions'] and not metrics['gate_extensions'], metrics
            counts['deadline_revert'] += 1
        # Without the memo an expired deadline leaves the exact boundary unknown for every policy.
        for policy in (1, 2, 3):
            metrics, _ = call(policy, None, 1e-12)
            assert metrics['status'] == 2 and metrics['lift'] == 0, metrics
            counts['unknown'] += 1
        # Non-adaptive policies ignore the memo.
        memo = _native.ResidualMemo()
        metrics, _ = call(1, memo)
        assert len(memo) == 0 and metrics['memo_hits'] == 0
    # With every primary already mixed no cost-one extension exists, so exact-only reaches d = 2.
    p4 = independent_columns(4)
    columns4 = [p4[0] & p4[1], *p4]
    # 6996 and 0116 need nine gates (verified optima); this boundary allows 1 + 7 = 8.
    for target, status in ((0x6996, 0), (0x0116, 0), (0x8000, 1)):
        metrics, _ = _native.slack_three_boundary(columns4, 1, list(p4), 15, types(p4), target, 0xffff,
                                                  2_000_000, 0, 5, True, 1)
        assert metrics['status'] == status, (target, metrics)
        if metrics['status'] == 0:
            assert metrics['lift'] == 2 and metrics['extension_total'] == len(types(p4)), metrics
            counts['no_free_exact'] += 1
    assert counts['no_free_exact'] == 2
    try:
        _native.slack_three_boundary([a, b], 1, [], 0, [], a, care, policy=4)
        raise AssertionError('policy 4 accepted')
    except ValueError:
        pass
    return dict(counts)


SETTINGS = [(mode, symmetric) for mode in (0, 2, 3, 4, 5) for symmetric in (False, True)]
# The decoder phase screen needs the parity filter (mode >= 1); mode 0 checks it stays inert.
DECODER_SETTINGS = [(mode, symmetric, decoder) for mode, symmetric in SETTINGS for decoder in (1, 2)]


def check():
    checks = decoder_checks = 0
    for k in (2, 3):
        full = (1 << (1 << k)) - 1
        for care in (full, full ^ 1, full ^ 17 if k == 3 else full ^ 2):
            for h in range(1, k + 1):
                columns = [col & care for col in independent_columns(k)]
                expected = dag_tables(columns, h, care, k + 2)
                for value in range(full + 1):
                    if value & ~care:
                        continue
                    for mode, symmetric, decoder in [(*s, 0) for s in SETTINGS] + DECODER_SETTINGS:
                        metrics, regions = _native.slack_three_boundary(
                            columns, h, [], 0, [], value, care, 2_000_000, 0, mode, symmetric, decoder=decoder)
                        assert metrics['status'] == (value in expected), (
                            columns, h, care, value, mode, symmetric, decoder)
                        assert bool(regions) == (metrics['status'] == 1)
                        if regions:
                            verify(columns, h, value, care, regions)
                        checks += 1
                        decoder_checks += bool(decoder)

    # Identical columns still describe distinct first-layer wires.
    duplicated = 0
    columns, care = [0x88, 0x88, 0xf0], 0xff
    expected = dag_tables(columns, 2, care, 5)
    for target in (0, 0x80, 0xf0, 0x7f, 0x88, 0x78):
        for mode, symmetric, decoder in [(*s, 0) for s in SETTINGS] + DECODER_SETTINGS:
            metrics, regions = _native.slack_three_boundary(
                columns, 2, [], 0, [], target, care, mode=mode, symmetric=symmetric, deadline_seconds=0,
                decoder=decoder)
            assert metrics['status'] == (target in expected), (target, mode, symmetric)
            if regions:
                verify(columns, 2, target, care, regions)
            duplicated += 1

    # Extensions: every retained/excluded decision is replayed independently.
    a, b, c, d, e = primaries = independent_columns(5)
    care = 0xffffffff
    gate_columns = types(primaries)
    columns = [a & b, c]
    extension_checks = 0
    for target in (a & b & c & d & e, (a & b & c) ^ d, (a & b) | (c & d & e), (a & b & c) ^ (d & e)):
        assert not feasible(columns, 1, target, care, 3)
        kept_mixed, kept_gates, counts = expected_extensions(columns, 1, primaries, 4, gate_columns, target, care)
        for mode, symmetric, decoder in [(2, False, 0), (5, False, 0), (5, True, 0), (4, False, 1), (4, False, 2),
                                         (5, True, 1)]:
            metrics, regions = _native.slack_three_boundary(
                columns, 1, primaries, 4, gate_columns, target, care, deadline_seconds=0, mode=mode,
                symmetric=symmetric, decoder=decoder)
            assert not regions and metrics['status'] == 0, metrics
            assert metrics['extension_unknown'] == 0, metrics
            assert (metrics['mixed_extensions'], metrics['gate_extensions']) == (kept_mixed, kept_gates), (
                target, metrics, kept_mixed, kept_gates)
            assert (metrics['extension_feasible'], metrics['extension_excluded'],
                    metrics['extension_subsumed']) == (counts['feasible'], counts['excluded'],
                                                       counts['subsumed']), (target, metrics, counts)
            extension_checks += 1
        # An exhausted work or time limit is unknown and never excludes anything.
        for limits in ((0, 0), (100_000, 1e-12)):
            metrics, regions = _native.slack_three_boundary(
                columns, 1, primaries, 4, gate_columns, target, care, *limits, 5, True)
            assert not regions and metrics['status'] == 2 and not metrics['extension_excluded'], metrics
            extension_checks += 1

    # A boundary wider than the engines' limit, or no first layer, is unknown.
    for args in ((list(primaries[:2]), 0), ([a] * 9, 1)):
        metrics, regions = _native.slack_three_boundary(args[0], args[1], [], 0, [], a, care)
        assert metrics['status'] == 2 and not regions
    for bad in (dict(mode=6), dict(decoder=3)):
        try:
            _native.slack_three_boundary([a, b], 1, [], 0, [], a, care, **bad)
        except ValueError:
            continue
        raise AssertionError(bad)
    print(json.dumps({'oracle_comparisons': checks, 'decoder_oracle_comparisons': decoder_checks,
                      'duplicated_wire_checks': duplicated,
                      'extension_and_limit_checks': extension_checks, 'argument_checks': 4,
                      'policy_checks': check_policies()}))


def replay(path, output, work_limit, deadline, limit, modes, repetitions):
    reference = SimpleNamespace(independent_columns=independent_columns)
    counts = Counter()
    with output.open('x', encoding='utf-8') as out:
        for name, record, first, mixed_ids, primaries, _, target, care in captured_boundaries(
                reference, path, limit, event='slack_three'):
            columns = [*first, *(primaries[i] for i in mixed_ids)]
            assert record['k'] == 2 * len(first) + len(mixed_ids) + 2
            gate_columns = types(primaries)
            decided, retained = set(), set()
            settings = [(mode, symmetric) for mode in modes for symmetric in (False, True)]
            for repetition in range(repetitions):
                offset = repetition % len(settings)
                for mode, symmetric in (*settings[offset:], *settings[:offset]):
                    start = perf_counter()
                    metrics, regions = _native.slack_three_boundary(
                        columns, len(first), primaries, record['mixed'], gate_columns, target, care,
                        work_limit, deadline, mode, symmetric)
                    elapsed = perf_counter() - start
                    if metrics['status'] != 2:
                        decided.add(metrics['status'])
                    if metrics['status'] == 0 and metrics['extension_unknown'] == 0:
                        retained.add((metrics['mixed_extensions'], metrics['gate_extensions']))
                    if metrics['status'] == 1:
                        verify(columns, len(first), target, care, regions)
                    counts[(mode, symmetric, metrics['status'])] += 1
                    out.write(json.dumps(dict(record, **metrics, name=name, mode=mode, symmetric=symmetric,
                                              repetition=repetition, wall_seconds=elapsed,
                                              deadline_seconds=deadline, work_limit=work_limit)) + '\n')
            assert len(decided) <= 1, (name, record, decided)
            # Fully decided extension sets are a property of the boundary, not of the solver.
            assert len(retained) <= 1, (name, record, retained)
    print(json.dumps({f'{mode}/{"sym" if sym else "dir"}/{status}': count
                      for (mode, sym, status), count in sorted(counts.items())}))


POLICY_NAMES = ('full', 'exact', 'lift1', 'adaptive')


def replay_decoder(path, output, work_limit, deadline, limit, mode, symmetric, policy, repetitions):
    """Replay captured boundaries with decoder phase screens 0, 1 and 2 under one policy.

    The exact Engine(., 3) query is timed separately (exact_seconds) from the whole call; the
    remainder is extension cost. Decided verdicts and fully decided retained sets must agree.
    """
    reference = SimpleNamespace(independent_columns=independent_columns)
    totals = {decoder: Counter() for decoder in (0, 1, 2)}
    with output.open('x', encoding='utf-8') as out:
        for name, record, first, mixed_ids, primaries, _, target, care in captured_boundaries(
                reference, path, limit, event='slack_three'):
            columns = [*first, *(primaries[i] for i in mixed_ids)]
            gate_columns = types(primaries)
            results = {}
            for repetition in range(repetitions):
                order = (0, 1, 2)[repetition % 3:] + (0, 1, 2)[:repetition % 3]
                for decoder in order:
                    start = perf_counter()
                    metrics, regions = _native.slack_three_boundary(
                        columns, len(first), primaries, record['mixed'], gate_columns, target, care,
                        work_limit, deadline, mode, symmetric, policy, None, decoder)
                    elapsed = perf_counter() - start
                    if metrics['status'] == 1:
                        verify(columns, len(first), target, care, regions)
                    results.setdefault(decoder, []).append((metrics, elapsed))
                    out.write(json.dumps(dict(record, **metrics, name=name, decoder=decoder, mode=mode,
                                              symmetric=symmetric, policy=POLICY_NAMES[policy],
                                              repetition=repetition, wall_seconds=elapsed,
                                              deadline_seconds=deadline, work_limit=work_limit)) + '\n')
            decided, retained = set(), set()
            for decoder, runs in results.items():
                # Median repetition by wall time; its counters are reported.
                runs.sort(key=lambda run: run[1])
                metrics, elapsed = runs[len(runs) // 2]
                for m, _ in runs:
                    if m['status'] != 2:
                        decided.add(m['status'])
                    if m['status'] == 0 and m['extension_unknown'] == 0 and policy == 0:
                        retained.add((m['mixed_extensions'], m['gate_extensions']))
                total = totals[decoder]
                total['boundaries'] += 1
                total[f'status{metrics["status"]}'] += 1
                total['wall_ms'] += 1000 * elapsed
                total['exact_ms'] += 1000 * metrics['exact_seconds']
                total['extension_ms'] += 1000 * (elapsed - metrics['exact_seconds'])
                total['exact_work'] += metrics['work']
                total['tree_calls'] += metrics['tree_calls']
                total['extension_calls'] += (metrics['tight_calls'] + metrics['slack_one_calls']
                                             + metrics['slack_two_calls'])
                total['slack_two_work'] += metrics['slack_two_work']
                if metrics['status'] == 0:
                    total[f'lift{metrics["lift"]}'] += 1
                for key in ('decoder_screens', 'decoder_rejects', 'decoder_column_rejects', 'decoder_skipped',
                            'decoder_work'):
                    total[key] += metrics[key]
            assert len(decided) <= 1, (name, record, {d: [m['status'] for m, _ in r] for d, r in results.items()})
            assert len(retained) <= 1, (name, record, retained)
    print(json.dumps({decoder: {key: round(value, 1) if isinstance(value, float) else value
                                for key, value in sorted(total.items())} for decoder, total in totals.items()}))


def replay_policies(path, output, work_limit, deadline, limit, mode, symmetric):
    """Replay captured boundaries under each lazy policy; adaptive shares one memo per target."""
    reference = SimpleNamespace(independent_columns=independent_columns)
    totals = {name: Counter() for name in POLICY_NAMES}
    memos = {}
    with output.open('x', encoding='utf-8') as out:
        for name, record, first, mixed_ids, primaries, _, target, care in captured_boundaries(
                reference, path, limit, event='slack_three'):
            columns = [*first, *(primaries[i] for i in mixed_ids)]
            gate_columns = types(primaries)
            memo = memos.setdefault((name, target, care), _native.ResidualMemo())
            results = {}
            for policy, policy_name in enumerate(POLICY_NAMES):
                start = perf_counter()
                metrics, regions = _native.slack_three_boundary(
                    columns, len(first), primaries, record['mixed'], gate_columns, target, care,
                    work_limit, deadline, mode, symmetric, policy, memo if policy == 3 else None)
                elapsed = perf_counter() - start
                if metrics['status'] == 1:
                    verify(columns, len(first), target, care, regions)
                results[policy_name] = metrics
                calls = metrics['tight_calls'] + metrics['slack_one_calls'] + metrics['slack_two_calls']
                total = totals[policy_name]
                total['boundaries'] += 1
                total[f'status{metrics["status"]}'] += 1
                total['wall_ms'] += 1000 * elapsed
                total['extension_calls'] += calls
                total['covered'] += metrics['covered']
                total['memo_hits'] += metrics['memo_hits']
                if metrics['status'] == 0:
                    total[f'lift{metrics["lift"]}'] += 1
                    total['retained_mixed_bits'] += bin(metrics['mixed_extensions']).count('1')
                    total['retained_gate_bits'] += bin(metrics['gate_extensions']).count('1')
                out.write(json.dumps(dict(record, **metrics, name=name, policy=policy_name, mode=mode,
                                          symmetric=symmetric, wall_seconds=elapsed, deadline_seconds=deadline,
                                          work_limit=work_limit, extension_calls=calls)) + '\n')
            full = results['full']
            decided = {m['status'] for m in results.values() if m['status'] != 2}
            assert len(decided) <= 1, (name, record, results)
            if full['status'] == 0 and full['extension_unknown'] == 0:
                for policy_name in POLICY_NAMES[1:]:
                    m = results[policy_name]
                    if m['status'] == 0:
                        # Lazy policies retain only elements of feasible extensions.
                        assert m['mixed_extensions'] & ~full['mixed_extensions'] == 0, (name, policy_name, m)
                        assert m['gate_extensions'] & ~full['gate_extensions'] == 0, (name, policy_name, m)
                        if m['lift'] == 4 and m['extension_unknown'] == 0:
                            totals[policy_name]['pure_equal_full'] += (
                                (m['mixed_extensions'], m['gate_extensions'])
                                == (full['mixed_extensions'], full['gate_extensions']))
    print(json.dumps({name: {key: round(value, 1) if isinstance(value, float) else value
                             for key, value in sorted(total.items())} for name, total in totals.items()}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--work-limit', type=int, default=2_000_000)
    parser.add_argument('--deadline', type=float, default=0.025)
    parser.add_argument('--limit', type=int, default=128)
    parser.add_argument('--memory-mib', type=int, default=512)
    parser.add_argument('--modes', type=int, nargs='+', choices=range(6), default=[4, 5])
    parser.add_argument('--repetitions', type=int, default=1)
    parser.add_argument('--policies', action='store_true',
                        help='replay full/exact/lift1/adaptive policies with the first --modes entry')
    parser.add_argument('--directed', action='store_true', help='with --policies, use directed trees')
    parser.add_argument('--decoder', choices=POLICY_NAMES,
                        help='replay decoder phase screens 0/1/2 under this policy with the first --modes entry')
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error('--repetitions must be positive')
    limit_commit_mib(args.memory_mib)
    if args.capture:
        if not args.output:
            parser.error('--capture requires --output')
        if args.decoder:
            replay_decoder(args.capture, args.output, args.work_limit, args.deadline, args.limit, args.modes[0],
                           not args.directed, POLICY_NAMES.index(args.decoder), args.repetitions)
        elif args.policies:
            replay_policies(args.capture, args.output, args.work_limit, args.deadline, args.limit,
                            args.modes[0], not args.directed)
        else:
            replay(args.capture, args.output, args.work_limit, args.deadline, args.limit, args.modes,
                   args.repetitions)
    else:
        check()
