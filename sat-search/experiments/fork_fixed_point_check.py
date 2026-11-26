"""Check the reduction to linear, fully genuine fork mode CNFs."""

import json
from collections import Counter, defaultdict
from itertools import combinations, product
from random import Random


def normalize_width(clauses):
    """Eliminate units with a fresh variable that has a unique satisfying value."""
    if () in clauses:
        return tuple(product((1, -1), (2, -2)))
    next_var = max((abs(lit) for clause in clauses for lit in clause), default=0) + 1
    result = []
    for clause in clauses:
        if len(clause) == 1:
            (lit,) = clause
            result.extend(((lit, next_var), (lit, -next_var), (-lit, -next_var)))
            next_var += 1
        else:
            result.append(clause)
    return tuple(result)


def compile_modes(clauses):
    copies = defaultdict(list)
    replica_groups = [[] for _ in range(3 * len(clauses))]
    next_copy = 1
    for group, clause in enumerate(clauses):
        for lit in clause:
            for replica in range(3):
                flip = lit > 0
                copies[abs(lit)].append((next_copy, flip))
                replica_groups[3 * group + replica].append(-next_copy)
                next_copy += 1

    def renamed(copy_info):
        copy, flip = copy_info
        return -copy if flip else copy

    links = []
    for cycle in copies.values():
        for first, second in zip(cycle, cycle[1:] + cycle[:1]):
            links.append((-renamed(first), renamed(second)))
    return tuple(map(tuple, replica_groups)) + tuple(links), copies


def models(clauses):
    variables = sorted({abs(lit) for clause in clauses for lit in clause})
    return {
        tuple(zip(variables, bits))
        for bits in product((False, True), repeat=len(variables))
        if satisfies(clauses, dict(zip(variables, bits)))
    }


def satisfies(clauses, values):
    return all(any(values[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses)


def enumerate_modes(clauses, assignment):
    """Enumerate the target models by clause simplification and unit propagation."""
    if not clauses:
        yield assignment
        return
    clause = min(clauses, key=len)
    if not clause:
        return
    lit = clause[0]
    for choice in ((lit,) if len(clause) == 1 else (lit, -lit)):
        reduced = tuple(
            tuple(other for other in clause if other != -choice)
            for clause in clauses if choice not in clause
        )
        yield from enumerate_modes(reduced, {**assignment, abs(choice): choice > 0})


def check_structure(clauses, copy_count):
    # Vertices are literal slots. Group incidence comes from the slot's clause index.
    slots = defaultdict(list)
    seen_pairs = set()
    for group, clause in enumerate(clauses):
        assert 2 <= len(clause) <= 3
        assert len(set(map(abs, clause))) == len(clause)
        for pair in combinations(sorted(map(abs, clause)), 2):
            assert pair not in seen_pairs
            seen_pairs.add(pair)
        for lit in clause:
            slots[lit].append(group)
    assert sum(map(len, clauses)) == 3 * copy_count
    recovered = [[] for _ in clauses]
    for copy in range(1, copy_count + 1):
        (center,) = slots[copy]
        left, right = slots[-copy]
        assert len({center, left, right}) == 3
        recovered[center].append(copy)
        recovered[left].append(-copy)
        recovered[right].append(-copy)
    assert [set(clause) for clause in recovered] == [set(clause) for clause in clauses]


def check_instance(source):
    normalized = normalize_width(source)
    target, copies = compile_modes(normalized)
    copy_count = sum(map(len, copies.values()))
    assert copy_count == 3 * sum(map(len, normalized))
    check_structure(target, copy_count)
    expected = models(source)
    original_variables = {abs(lit) for clause in source for lit in clause}
    found = set()
    for mode in enumerate_modes(target, {}):
        assert len(mode) == copy_count and satisfies(target, mode)
        decoded = {}
        for var, cycle in copies.items():
            values = {mode[copy] ^ flip for copy, flip in cycle}
            assert len(values) == 1
            if var in original_variables:
                decoded[var] = values.pop()
        source_model = tuple(sorted(decoded.items()))
        assert source_model not in found
        found.add(source_model)
    assert found == expected
    return bool(found), copy_count


def main():
    rng = Random(261126)
    alphabet = ((1,), (-1,), (2,), (-2,), (1, 2), (1, -2), (-1, 2), (-1, -2))
    results = Counter()
    for mask in range(1 << len(alphabet)):
        formula = tuple(clause for i, clause in enumerate(alphabet) if mask >> i & 1)
        sat, copies = check_instance(formula)
        results["exhaustive"] += 1
        results["satisfiable"] += sat
        results["copies"] += copies
    for _ in range(400):
        n = rng.randrange(1, 7)
        formula = tuple(
            tuple(rng.choice((-1, 1)) * rng.randrange(1, n + 1) for _ in range(rng.randrange(1, 4)))
            for _ in range(rng.randrange(1, 10))
        )
        sat, copies = check_instance(formula)
        results["random"] += 1
        results["satisfiable"] += sat
        results["copies"] += copies
    check_instance(((), (1, -2)))
    results["empty_clause"] += 1
    print(json.dumps(dict(results), sort_keys=True))


if __name__ == "__main__":
    main()
