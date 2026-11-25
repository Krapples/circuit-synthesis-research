"""Native (C++20, sat-search/native) regional completion kernel, opt-in.

local_blocks_native has the contract of regional_block_completion.local_blocks with the production flags
(port_first=True, witness_cover=True, row_quotient=True by default; module_filter as given): exact occurrence
semantics, signed phases, witness trees ('x', i, neg) / (op, a, b), same algorithm and search order, one
Python -> C++ call per query.  The read-once prelude (targets' recognized trees, learned phases, forced &/|
adjacency) runs here in Python, unchanged from the reference, and is passed in.  Queries outside the native ranges
(m > 8, > 16 providers, > 64 rows) fall back to the Python reference.

Deadlines: the native search polls PyErr_CheckSignals(), so regional_deadline.timed raises KeyboardInterrupt out of
the call as for Python code; a timeout is never reported as UNSAT.  work_limit raises CompletionWorkLimit.

Completion modes (ordered_quotient_core.make_completion), same decisions and witnesses as the Python modes:
  'native-row-quotient'   (= 'row-quotient')  completion_native(adaptive=False): one native call per cache miss
  'native-phase-first'    (= 'phase-first')   completion_native(adaptive=True): prelude, phase classes and every
                                              monotone local_blocks call in one native call per cache miss
  'native-a-phase-first'  stage A only: Python phase-first loop calling local_blocks_native per monotone call
Build: & "sat-search\\native\\build_native.bat" (see sat-search/NOTES_NATIVE.md).
"""
import os
import sys
from collections import Counter

from regional_block_completion import CompletionWorkLimit, indices, local_blocks
from two_sharing_core import ANY, tree

_NATIVE_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'native')
if _NATIVE_DIR not in sys.path:
    sys.path.insert(0, _NATIVE_DIR)
try:
    import _regional_native as _native
except ImportError:          # not built: callers must check available()
    _native = None

STAT_KEYS = ('rec', 'row_reject', 'module_reject', 'port_allocations', 'port_allocation_reject', 'partition_checks',
             'endpoint_split_reject', 'dominance_split_reject', 'obligation_partitions', 'cover_nodes',
             'quotient_conflicts', 'quotient_dropped')
_MASK64 = (1 << 64) - 1


def available():
    return _native is not None


def prelude(m, targets, signed):
    """Phases and forced adjacency learned from the targets' read-once trees (local_blocks lines 'learn' ... 'tree').
    Returns (phase dict, forced dict) or None when the reference returns None before searching."""
    one = (1 << (1 << m)) - 1
    phase = {}
    forced = {'&': [0] * m, '|': [0] * m}

    def learn(node):
        if node[0] == 'x':
            _, i, neg = node
            if i in phase and phase[i] != neg:
                return None
            phase[i] = neg
            return 1 << i
        op, *children = node
        opposite = '|' if op == '&' else '&'
        seen = 0
        for child in children:
            used = learn(child)
            if used is None:
                return None
            for i in indices(used):
                if forced[opposite][i] & seen:
                    return None
                forced[op][i] |= seen
            for i in indices(seen):
                forced[op][i] |= used
            seen |= used
        return seen

    for target in set(targets) - {0, one, ANY}:
        recognized = tree(m, target, signed)
        if recognized is None or learn(recognized) is None:
            return None
    return phase, forced


def local_blocks_native(m, ports, pats, targets, signed, stats=None, module_filter=True, *, row_quotient=True,
                        work_limit=None, native_stats=None):
    counts = Counter(ports)
    providers = tuple(sorted(counts))
    if (_native is None or m > _native.MAX_M or len(providers) > _native.MAX_PROVIDERS
            or not 1 <= len(pats) <= _native.MAX_ROWS or any(c > 255 for c in counts.values())):
        if stats is not None:
            stats['native_fallbacks'] += 1
        return local_blocks(m, ports, pats, targets, signed, stats, module_filter, port_first=True,
                            witness_cover=True, row_quotient=row_quotient, work_limit=work_limit)
    if stats is not None:
        stats['local'] += 1
    learned = prelude(m, targets, signed)
    if learned is None:
        return None
    phase, forced = learned
    compact = tuple(sum((p >> q & 1) << k for k, q in enumerate(providers)) for p in pats)
    words = []
    for t in targets:
        if t == ANY:
            words += (0, 0, 0, 0)
        else:
            words += (t & _MASK64, t >> 64 & _MASK64, t >> 128 & _MASK64, t >> 192 & _MASK64)
    status, witness, st = _native.solve_blocks(
        m, list(providers), [counts[i] for i in providers], list(compact), [int(t == ANY) for t in targets], words,
        bool(signed), bool(module_filter), bool(row_quotient), [int(phase[i]) if i in phase else -1 for i in range(m)],
        forced['&'], forced['|'], -1 if work_limit is None else int(work_limit), 0.0)
    if stats is not None:
        for key in STAT_KEYS:
            if st[key]:
                stats[key] += st[key]
    if native_stats is not None:
        native_stats.update(st)
    if status == 3:
        raise CompletionWorkLimit
    if status == 2:
        raise KeyboardInterrupt      # native deadline (unused by default); never UNSAT
    return witness


STAGE_B_KEYS = STAT_KEYS + ('local', 'phase_first_calls', 'phase_clauses', 'phase_nodes', 'phase_classes',
                            'monotone_calls', 'phase_reject')


def _encode(m, ports, pats, targets):
    counts = Counter(ports)
    providers = tuple(sorted(counts))
    compact = [sum((p >> q & 1) << k for k, q in enumerate(providers)) for p in pats]
    words = []
    for t in targets:
        words += (0, 0, 0, 0) if t == ANY else (t & _MASK64, t >> 64 & _MASK64, t >> 128 & _MASK64, t >> 192 & _MASK64)
    return providers, [counts[i] for i in providers], compact, [int(t == ANY) for t in targets], words


def completion_native(m, ports, pats, targets, signed, stats=None, module_filter=True, *, adaptive=True,
                      native_stats=None):
    """Stage B: the whole completion-solver call in one native call -- read-once prelude, and either
    regional_phase_first.adaptive_completion (adaptive=True; phase_problem, phase_domains, virtual-port recoding,
    monotone local_blocks, lift) or local_blocks with the production flags (adaptive=False).  The phase-first
    witness is re-checked with check_tree, as the reference does.  Out-of-range queries use the Python reference."""
    providers = set(ports)
    if (_native is None or m > _native.MAX_M or len(providers) > 16 or not 1 <= len(pats) <= _native.MAX_ROWS
            or any(c > 255 for c in Counter(ports).values())):
        if stats is not None:
            stats['native_fallbacks'] += 1
        if adaptive:
            from regional_phase_first import adaptive_completion
            return adaptive_completion(m, ports, pats, targets, signed, stats, module_filter)
        return local_blocks(m, ports, pats, targets, signed, stats, module_filter, port_first=True,
                            witness_cover=True, row_quotient=True)
    prov, counts, compact, anys, words = _encode(m, ports, pats, targets)
    status, witness, st = _native.solve_completion(m, list(prov), counts, compact, anys, words, bool(signed),
                                                   bool(module_filter), bool(adaptive))
    if stats is not None:
        for key in STAGE_B_KEYS:
            if st[key]:
                stats[key] += st[key]
    if native_stats is not None:
        native_stats.update(st)
    if status == 2:
        raise KeyboardInterrupt      # aborted by a poll: never reported as UNSAT
    if witness is not None and st['phase_first_calls']:
        from regional_production_adapter import check_tree
        check_tree(witness, m, ports, pats, targets, True)
    return witness


def native_prelude(m, targets, signed):
    """Native counterpart of prelude() (for differential tests): None or (phase dict, forced dict)."""
    _, _, _, anys, words = _encode(m, (), (0,) * len(targets), targets)
    ok, phase, fa, fo = _native.prelude(m, anys, words, bool(signed))
    if not ok:
        return None
    return {i: bool(p) for i, p in enumerate(phase) if p >= 0}, {'&': list(fa), '|': list(fo)}


def native_adaptive_completion(m, ports, pats, targets, signed, stats=None, module_filter=True):
    """Stage A: regional_phase_first.adaptive_completion (Python) with local_blocks replaced by local_blocks_native."""
    from regional_phase_first import phase_first, phase_rule
    if signed and m + len(ports) > 0 and phase_rule(m, ports, targets):
        if stats is not None:
            stats['phase_first_calls'] += 1
        mono = lambda mm, p, ps, ts: local_blocks_native(mm, p, ps, ts, False, stats, module_filter)
        return phase_first(m, ports, pats, targets, stats, mono)
    return local_blocks_native(m, ports, pats, targets, signed, stats, module_filter)
