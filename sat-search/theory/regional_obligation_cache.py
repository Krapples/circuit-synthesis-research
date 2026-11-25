"""Bounded reusable completion cache for fixed regional obligations."""

from collections import Counter, defaultdict, deque
from functools import lru_cache
from itertools import permutations, product
from math import factorial, prod

from two_sharing_core import ANY, local


class ObligationCache:
    def __init__(self, mode='columns', maxsize=4096, *, solver=local, symmetry_limit=32):
        if mode not in ('dense', 'columns') or maxsize < 0 or symmetry_limit < 1:
            raise ValueError('invalid regional cache configuration')
        self.mode = mode
        self.solver = solver
        self.symmetry_limit = symmetry_limit
        self.stats = Counter()
        self.solve = lru_cache(maxsize=maxsize)(self._solve)
        self._normalize_cached = lru_cache(maxsize=maxsize)(self._normalize)

    def _solve(self, m, ports, patterns, targets, signed, module_filter):
        return self.solver(m, ports, patterns, targets, signed, self.stats, module_filter)

    def _normalize(self, ports, patterns, targets, signed):
        counts = Counter(ports)
        mask = sum(1 << i for i in counts)
        obligations = {}
        for pattern, target in zip(patterns, targets):
            if target == ANY:
                continue
            pattern &= mask
            if pattern in obligations and obligations[pattern] != target:
                return None
            obligations[pattern] = target
        rows = tuple(sorted(obligations.items(), key=lambda row: (row[1], row[0]))) or ((0, ANY),)
        if self.mode == 'dense':
            dense = tuple(((i, False),) * count for i, count in sorted(counts.items()))
            columns = tuple(sum((p >> members[0][0] & 1) << j for j, (p, _) in enumerate(rows)) for members in dense)
            return self._pack(rows, columns, dense)

        colors = defaultdict(int)
        for j, (_, target) in enumerate(rows):
            colors[target] |= 1 << j
        color_masks = tuple(colors.values())
        full = (1 << len(rows)) - 1
        groups = defaultdict(list)
        signatures = {}
        for i, count in sorted(counts.items()):
            column = sum((p >> i & 1) << j for j, (p, _) in enumerate(rows))
            signature = tuple((column & color).bit_count() for color in color_masks)
            dual = tuple(color.bit_count() - n for color, n in zip(color_masks, signature))
            phase = signed and (dual, column ^ full) < (signature, column)
            if phase:
                column ^= full
                signature, dual = dual, signature
            groups[column].extend(((i, phase),) * count)
            signatures[column] = (signature, signed and signature == dual)
        if not groups:
            return self._pack(rows, (), ())

        buckets = defaultdict(list)
        for column, members in groups.items():
            signature, balanced = signatures[column]
            buckets[len(members), signature].append((column, tuple(members), balanced))
        classes = [tuple(sorted(entries)) for _, entries in sorted(buckets.items())]
        flips = sum(int(balanced) for entries in classes for _, _, balanced in entries)
        variants = prod(factorial(len(entries)) for entries in classes) << flips
        if variants > self.symmetry_limit:
            # Compact exact key even when canonical tie-breaking is capped.
            # This can miss an isomorphic cache hit, never change the verdict.
            self.stats['symmetry_capped'] += 1
            entries = [entry for bucket in classes for entry in bucket]
            return self._pack(rows, tuple(c for c, _, _ in entries), tuple(m for _, m, _ in entries))

        best = None
        for ordering in product(*(permutations(entries) for entries in classes)):
            entries = tuple(entry for bucket in ordering for entry in bucket)
            for phases in product(*((False, True) if balanced else (False,) for _, _, balanced in entries)):
                columns = tuple(column ^ (full if flip else 0) for (column, _, _), flip in zip(entries, phases))
                members = tuple(tuple((i, phase ^ flip) for i, phase in group)
                                for (_, group, _), flip in zip(entries, phases))
                encoded = self._pack(rows, columns, members)
                if best is None or encoded[:2] < best[:2]:
                    best = encoded
        return best

    @staticmethod
    def _pack(rows, columns, members):
        normalized = tuple(sorted((sum((column >> j & 1) << i for i, column in enumerate(columns)), t)
                                  for j, (_, t) in enumerate(rows)))
        if len({pattern for pattern, _ in normalized}) != len(normalized):
            raise AssertionError('column equivalence did not preserve the observed row identities')
        return (tuple(p for p, _ in normalized), tuple(t for _, t in normalized), members)

    def __call__(self, m, ports, patterns, targets, signed, stats=None, module_filter=True):
        if len(patterns) != len(targets):
            raise ValueError('expected one target per observed pattern')
        self.stats['queries'] += 1
        if stats is not None:
            stats['local'] += 1
        normalized = self._normalize_cached(tuple(ports), tuple(patterns), tuple(targets), signed)
        if normalized is None:
            self.stats['obligation_conflicts'] += 1
            return None
        pats, values, members = normalized
        compact_ports = tuple(i for i, group in enumerate(members) for _ in group)
        tree = self.solve(m, compact_ports, pats, values, signed, module_filter)
        if tree is None:
            return None
        queues = [deque(group) for group in members]

        def lift(node):
            if node[0] == 'x':
                if node[1] < m:
                    return node
                provider, complemented = queues[node[1] - m].popleft()
                return 'x', m + provider, bool(node[2] ^ complemented)
            return node[0], *(lift(child) for child in node[1:])

        result = lift(tree)
        if any(queues):
            raise RuntimeError('completion dropped a port occurrence')
        return result

    def metrics(self):
        shared, normalized = self.solve.cache_info(), self._normalize_cached.cache_info()
        return dict(self.stats, cache_hits=shared.hits, cache_misses=shared.misses,
                    cache_entries=shared.currsize, normalization_hits=normalized.hits,
                    normalization_entries=normalized.currsize)
