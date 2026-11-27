"""Reuse the two cofactors of each outside formula across its possible modules."""

import json
from time import perf_counter

from read_once_core import INPUTS, PAIRS, TARGET, read_once


def dominates(columns, positive, negative):
    return all(not (value >> positive & 1) or (value >> negative & 1) for value in columns)


def forced_rows(outside):
    positive_rows = [i for i in range(len(PAIRS)) if TARGET >> i & 1]
    negative_rows = [i for i in range(len(PAIRS)) if not (TARGET >> i & 1)]
    forced_on, forced_off = set(), set()
    for positive in positive_rows:
        for negative in negative_rows:
            if dominates(outside, positive, negative):
                forced_on.add(positive)
                forced_off.add(negative)
    return forced_on, forced_off


def main():
    start = perf_counter()
    width = len(PAIRS)
    full = (1 << width) - 1
    cofactor_counts = {}
    surviving_requirements = {}
    surviving_scopes = {}
    module_choices = {}
    comparisons = 0
    ordinary = read_once(tuple(sorted(INPUTS)))
    if TARGET in ordinary:
        raise AssertionError("the all-input module reaches the target")
    for bits in range(1, 1 << len(INPUTS)):
        inner = tuple(sorted(v for i, v in enumerate(INPUTS) if bits & (1 << i)))
        outside = tuple(v for i, v in enumerate(INPUTS) if not bits & (1 << i))
        on, off = forced_rows(outside)
        if any(dominates(inner, p, n) for p in on for n in off):
            continue
        surviving_scopes[len(inner)] = surviving_scopes.get(len(inner), 0) + 1
        if not outside:
            # The outer expression only sees two copies of a single value.
            continue
        inner_choices = tuple(sorted(value for value in read_once(inner)
                                     if all(value >> p & 1 for p in on)
                                     and all(not (value >> n & 1) for n in off)))
        module_choices[bits] = inner_choices
        outer = tuple(sorted([full << width, full << width, *(v | (v << width) for v in outside)]))
        cofactors = read_once(outer)
        cofactor_counts[len(inner)] = cofactor_counts.get(len(inner), 0) + len(cofactors)
        requirements = set()
        for pair in cofactors:
            low, high = pair & full, pair >> width
            assert (low & ~high) == 0
            if (low & ~TARGET) == 0 and (TARGET & ~high) == 0:
                requirements.add((TARGET & ~low, high & ~TARGET))
        surviving_requirements[len(inner)] = surviving_requirements.get(len(inner), 0) + len(requirements)
        if requirements:
            comparisons += len(inner_choices) * len(requirements)
            for required, forbidden in requirements:
                if any((required & ~value) == 0 and (forbidden & value) == 0 for value in inner_choices):
                    raise AssertionError(f"cofactor witness with module {bits}")
    print(json.dumps({
        "cofactor_counts_by_module_size": cofactor_counts,
        "surviving_requirements_by_module_size": surviving_requirements,
        "surviving_scopes_by_module_size": surviving_scopes,
        "proper_module_choices": module_choices,
        "module_comparisons": comparisons,
        "seconds": round(perf_counter() - start, 6),
    }))


if __name__ == "__main__":
    main()
