"""Necessary provider ownership for blocks of private variables."""


def block_requirements(blocks, rows, patterns, project, is_and, signed, portmask):
    """Return minimal provider masks that must each meet the block's child."""
    pairs = []
    for i, (row, table) in enumerate(rows):
        for j in range(i + 1 if signed else 0, len(rows)):
            other, target = rows[j]
            if table != target:
                a, b = patterns[row], patterns[other]
                pairs.append((i, j, (a ^ b if signed else a & ~b) & portmask))

    requirements = []
    for block in blocks:
        slices = tuple(project(table, block, is_and) for _, table in rows)
        if signed:
            needed = {mask for i, j, mask in pairs if slices[i] != slices[j]}
        else:
            needed = {mask for i, j, mask in pairs if slices[i] & ~slices[j]}
        minimal = []
        for mask in sorted(needed, key=lambda value: (value.bit_count(), value)):
            if not any(subset & mask == subset for subset in minimal):
                minimal.append(mask)
        requirements.append(tuple(minimal))
    return tuple(requirements)
