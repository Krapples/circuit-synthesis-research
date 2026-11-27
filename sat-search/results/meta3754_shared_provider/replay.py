"""Exhaustive local control for the L-meta-3754 protected-provider rewrite."""

import json


INPUTS = ("c", "u", "v", "d", "w", "b")
EDGES = (("v", "c"), ("c", "u"), ("u", "d"), ("d", "w"), ("w", "b"))
ORIGINAL = (
    ("P", "or", "u", "w"),
    ("A", "or", "P", "v"),
    ("B0", "or", "v", "b"),
    ("B", "or", "u", "B0"),
    ("J", "and", "A", "B"),
    ("K", "and", "J", "c"),
    ("Q", "and", "P", "d"),
    ("E", "and", "w", "b"),
    ("C0", "or", "K", "Q"),
    ("C", "or", "C0", "E"),
)


def evaluate(gates, assignment):
    values = {name: name in assignment for name in INPUTS}
    for name, op, lhs, rhs in gates:
        assert name not in values and lhs in values and rhs in values
        if op == "and":
            values[name] = values[lhs] and values[rhs]
        else:
            assert op == "or"
            values[name] = values[lhs] or values[rhs]
    return values


def target(assignment):
    return any(left in assignment and right in assignment for left, right in EDGES)


def ancestors(output, omitted=()):
    definitions = {name: (lhs, rhs) for name, _, lhs, rhs in ORIGINAL}
    reached = set()
    pending = [output]
    while pending:
        name = pending.pop()
        if name in reached or name in omitted or name not in definitions:
            continue
        reached.add(name)
        pending.extend(definitions[name])
    return reached


def rebuild(keep_all_providers=False, overwrite_protected=False, reuse_unfiltered=False):
    gates = []
    for gate in ORIGINAL:
        name, op, lhs, rhs = gate
        if name in {"A", "B0", "B"} and not keep_all_providers:
            continue
        if name == "P" and overwrite_protected:
            gate = ("P", "or", "u", "u")
        if name == "J":
            if not reuse_unfiltered:
                left = "P" if overwrite_protected else "u"
                gates.append(("R", "or", left, "v"))
            continue
        if name == "K":
            gate = (name, op, "A" if reuse_unfiltered else "R", rhs)
        gates.append(gate)
    return gates


def main():
    kept = ancestors("C", omitted={"J"})
    charged = ancestors("A") - kept
    assert kept == {"P", "K", "Q", "E", "C0", "C"} and charged == {"A"}
    variants = {
        "original": ORIGINAL,
        "protected_rebuild": rebuild(),
        "overwrite_protected": rebuild(overwrite_protected=True),
        "reuse_unfiltered": rebuild(keep_all_providers=True, reuse_unfiltered=True),
        "keep_all_and_append": rebuild(keep_all_providers=True),
    }
    mismatches = {name: [] for name in variants}
    changes_to_retained_provider = 0
    dirty = set()
    for mask in range(1 << len(INPUTS)):
        assignment = {name for i, name in enumerate(INPUTS) if mask >> i & 1}
        expected = target(assignment)
        original_values = evaluate(ORIGINAL, assignment)
        if not expected:
            dirty.update(name for name, op, _, _ in ORIGINAL if op == "and" and original_values[name])
        for name, gates in variants.items():
            values = evaluate(gates, assignment)
            if values["C"] != expected:
                mismatches[name].append([vertex for vertex in INPUTS if vertex in assignment])
            if name == "protected_rebuild":
                changes_to_retained_provider += values["P"] != original_values["P"]
    assert dirty == {"J"}
    assert not mismatches["original"] and not mismatches["protected_rebuild"]
    assert not mismatches["keep_all_and_append"] and len(variants["keep_all_and_append"]) == len(ORIGINAL)
    assert ["d", "w"] in mismatches["overwrite_protected"]
    assert ["c", "w"] in mismatches["reuse_unfiltered"]
    assert changes_to_retained_provider == 0
    print(json.dumps({
        "assignments": 1 << len(INPUTS),
        "edges": EDGES,
        "unique_dirty_and": sorted(dirty),
        "kept_gates": sorted(kept),
        "charged_chosen_cone": sorted(charged),
        "gates": {name: len(gates) for name, gates in variants.items()},
        "mismatches": mismatches,
        "changes_to_retained_provider": changes_to_retained_provider,
    }))


if __name__ == "__main__":
    main()
