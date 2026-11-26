"""Independent finite checks of robust identifier layout and bound arithmetic."""

from itertools import product

from mixed_sat_bound import sat


def unit(variable, positive):
    digits = f"{variable:b}"[::-1] if variable else ""
    return f"1{int(positive)}" + "".join(f"1{bit}" for bit in digits) + "0100"


def padding_plan(length):
    first = {0: [], 2: [1], 4: [2]}[length % 6]
    used = sum(len(unit(v, True)) for v in first)
    assert length >= 6 and used <= length and (length - used) % 6 == 0
    return first, (length - used) // 6


def check_layout():
    count = 0
    for width, tables in ((2, range(16)), (3, (0, 255, 0x96, 0xE8, 0x81, 0xFE))):
        high = 1 << width
        block_length = 2 * width + 8
        for table in tables:
            helpers = "".join(unit(high + row, False) for row in range(high) if not table >> row & 1)
            for blocks in range(1, 4):
                partial = len(helpers) + blocks * block_length
                first, zeros = padding_plan(6 + (-partial) % 6)
                pad = first + [0] * zeros
                suffix = "".join(unit(v, True) for v in pad)
                base = helpers + unit(high, True) * blocks + suffix
                free = [
                    len(helpers) + block * block_length + 3 + 2 * bit
                    for block in range(blocks) for bit in range(width)
                ]
                assert len(free) == len(set(free)) and len(base) % 6 == 0
                for rows in product(range(high), repeat=blocks):
                    direct = helpers + "".join(unit(high + row, True) for row in rows) + suffix
                    word = list(base)
                    for offset, (block, bit) in zip(free, product(range(blocks), range(width))):
                        word[offset] = str(rows[block] >> bit & 1)
                    assert "".join(word) == direct
                    assert sat(direct) == all(table >> row & 1 for row in rows)
                    count += 1
    return count


def check_arithmetic():
    count = 0
    for q in range(2, 15_000):
        n = 6 * q
        for r in range(8, n.bit_length()):
            length = 2 * r + 8
            d = r.bit_length() - 1 + 5
            blocks = n // length - 2**r - 1
            if blocks < 1:
                continue
            for helpers in (0, 2 ** (r - 1), 2**r):
                remainder = n - (helpers + blocks) * length
                first, zeros = padding_plan(remainder)
                assert sum(len(unit(v, True)) for v in first) + zeros * len(unit(0, True)) == remainder
            bound = n + blocks * max(0, 2 * r + 3 - 3 * d)
            assert 2 * n <= bound + n // length * (3 * d + 5) + (2**r + 2) * length
            count += 1
    return count


def check_example():
    n, r = 6 * 2**34, 24
    length = 2 * r + 8
    d = r.bit_length() - 1 + 5
    blocks = n // length - 2**r - 1
    assert blocks == 1_823_923_052
    bound = n + blocks * (2 * r + 3 - 3 * d)
    assert bound == 146_853_368_352 and bound > 17 * n // 12 - 4
    return n, bound


if __name__ == "__main__":
    print(f"PASS identifier layouts and independent SAT evaluations {check_layout()}")
    print(f"PASS feasible width and length combinations {check_arithmetic()}")
    print(f"PASS numeric example (length, lower bound) {check_example()}")
