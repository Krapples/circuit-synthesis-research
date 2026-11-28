"""Exact boundary rows for a complete monotone Boolean truth table."""


def monotone_frontier(table):
    """Return (minimal_true, maximal_false) in ascending bit-mask order.

    The table contains one value per assignment, indexed by its input bit
    mask. Reject tables that are not complete or not monotone.
    """
    size = len(table)
    if not size or size & (size - 1):
        raise ValueError("truth table length must be a power of two")
    bits = [1 << i for i in range(size.bit_length() - 1)]
    minimal_true = []
    maximal_false = []
    for row, value in enumerate(table):
        if value:
            if any(not table[row | bit] for bit in bits if not row & bit):
                raise ValueError("truth table must be monotone")
            if not any(table[row ^ bit] for bit in bits if row & bit):
                minimal_true.append(row)
        elif all(table[row | bit] for bit in bits if not row & bit):
            maximal_false.append(row)
    return minimal_true, maximal_false
