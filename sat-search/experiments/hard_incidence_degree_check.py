"""Exhaustive ANF checks for the hard-incidence degree and affine-core lift."""

import json
import random


SEED = 870069


def hard_sat(word, groups, width):
    """Evaluate by listing the witness assignments that satisfy each clause."""
    id_mask = (1 << width) - 1
    clauses = []
    for _ in range(groups):
        clause = []
        for _ in range(3):
            identifier = word & id_mask
            clause.append((identifier >> 1, identifier & 1))
            word >>= width
        clauses.append(clause)
    return any(
        all(any((witness >> var) & 1 == sign for var, sign in clause) for clause in clauses)
        for witness in range(1 << (1 << (width - 1)))
    )


def anf_degree(table):
    coefficients = bytearray(table)
    for bit in range((len(table) - 1).bit_length()):
        step = 1 << bit
        for base in range(0, len(table), 2 * step):
            for offset in range(step):
                coefficients[base + step + offset] ^= coefficients[base + offset]
    return max((mask.bit_count() for mask, c in enumerate(coefficients) if c), default=0)


def affine_lift_degree(table, nuisance_bits, rng):
    """Mix raw core and nuisance coordinates by invertible binary row operations."""
    core_bits = (len(table) - 1).bit_length()
    bits = core_bits + nuisance_bits
    rows = [1 << bit for bit in range(bits)]
    rng.shuffle(rows)
    for _ in range(4 * bits):
        target, source = rng.sample(range(bits), 2)
        rows[target] ^= rows[source]
    offset = rng.randrange(len(table))
    lifted = bytearray(len(table) << nuisance_bits)
    image = set()
    for parameters in range(len(lifted)):
        core = offset
        for bit, row in enumerate(rows[:core_bits]):
            core ^= ((row & parameters).bit_count() & 1) << bit
        image.add(core)
        lifted[parameters] = table[core]
    assert len(image) == len(table)
    return anf_degree(lifted), len(lifted)


def main():
    rng = random.Random(SEED)
    profiles = []
    raw_evaluations = 0
    lifted_evaluations = 0
    for groups, width in [(1, 1), (1, 3), (2, 1), (3, 1), (6, 1),
                          (2, 2), (3, 2), (2, 3)]:
        bits = 3 * groups * width
        table = bytearray(hard_sat(word, groups, width) for word in range(1 << bits))
        degree = anf_degree(table)
        expected = 0 if groups == 1 else bits - width
        assert degree == expected, (groups, width, degree, expected)
        pinned_slot_parities = [sum(table[value::1 << width]) % 2 for value in range(1 << width)]
        assert pinned_slot_parities == [int(groups >= 2)] * (1 << width)
        raw_evaluations += len(table)
        lifts = 0
        if 2 <= groups and bits <= 12:
            for _ in range(8):
                lifted_degree, evaluations = affine_lift_degree(table, 2, rng)
                assert lifted_degree == degree
                lifted_evaluations += evaluations
                lifts += 1
        profiles.append({"groups": groups, "width": width, "degree": degree,
                         "expected_degree": expected, "pinned_slot_parities": pinned_slot_parities,
                         "affine_lifts": lifts})
    print(json.dumps({"seed": SEED, "raw_evaluations": raw_evaluations,
                      "lifted_evaluations": lifted_evaluations, "profiles": profiles}, indent=2))


if __name__ == "__main__":
    main()
