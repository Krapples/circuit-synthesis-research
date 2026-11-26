"""Audit complete-table AIG reader bounds and replay the 07e1 witness."""
import json
import sys
from functools import cache
from itertools import combinations, permutations, product
from pathlib import Path
from random import Random
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'theory'))
from first_gate_bound import _lower, identify, support, trim
from module_contraction import brute, cofactor1
from signed_region_bounds import Bound, subs
from xor_factor import strip_xor

PHASES = tuple(product(range(2), repeat=2))


def recurrence(exact, regional=False, extension='baseline'):
    @cache
    def solve(n, f):
        if n <= 1:
            return 0
        if n <= 3 and exact is not None:
            return exact[n][f]
        if n == 2:
            return 3 if f == 6 else 1

        cof = [[cofactor1(n, f, i, phase) for phase in range(2)] for i in range(n)]
        supports = [[support(n - 1, g) for g in row] for row in cof]
        costs = [[lower(n - 1, g) for g in row] for row in cof]
        full = (1 << (1 << (n - 1))) - 1
        nonconstant = [all(g not in (0, full) for g in row) for row in cof]
        common = n - 1 + (Bound(n, f).lower() if regional else 0)
        for i, (slices, variables, bounds) in enumerate(zip(cof, supports, costs)):
            common = max(common, *(v + n - max(1, len(s)) for v, s in zip(bounds, variables)))
            if nonconstant[i]:
                common = max(common, min(bounds) + 2)
            if slices[0] ^ slices[1] == full:
                common = max(common, min(bounds) + 3)

        best = float('inf')
        for i, j in combinations(range(n), 2):
            ids = [lower(n - 1, identify(n, f, i, j, p)) for p in range(2)]
            if extension in ('profiles', 'phases'):
                double = max(lower(n - 2, cofactor1(n - 1, cof[i][a], j - 1, b))
                             for a, b in PHASES)
            shared = []
            for a, b in PHASES:
                need_i = i in supports[j][b]
                need_j = j - 1 in supports[i][a]
                v = max(common, costs[i][a] + 2, costs[j][b] + 2,
                        ids[a ^ b] + 1, ids[1 ^ a ^ b] + 2)
                for k, need in ((i, need_i), (j, need_j)):
                    if need:
                        v = max(v, max(costs[k]) + 2)
                        if nonconstant[k]:
                            v = max(v, min(costs[k]) + 3)
                if extension != 'baseline':
                    v = max(v, costs[i][a] + 2 + need_i, costs[j][b] + 2 + need_j)
                if extension in ('profiles', 'phases'):
                    separate = max(v, double + 2 + need_i + need_j,
                                   costs[i][1 - a] + 1 + need_i, costs[j][1 - b] + 1 + need_j)
                    together = max(v, double + 3, costs[i][a] + 3, costs[j][b] + 3,
                                   costs[i][1 - a] + 2, costs[j][1 - b] + 2,
                                   ids[a ^ b] + 2, ids[1 ^ a ^ b] + 3)
                    shared.append(together)
                    v = min(separate, together) if extension == 'profiles' else separate
                best = min(best, v)
            if extension == 'phases':
                # At least two distinct minterms on this pair have the D=1 profile.
                best = min(best, sorted(shared)[1])
        return best

    def lower(n, f):
        return solve(*trim(n, f))

    return lower


def evaluate(row, n):
    table = 0
    for assignment in range(1 << n):
        wires = [0] + [(assignment >> i) & 1 for i in range(n)]

        def read(literal):
            return wires[literal // 2] ^ (literal & 1)

        for a, b in row['gates']:
            assert 0 <= a // 2 < len(wires) and 0 <= b // 2 < len(wires)
            wires.append(read(a) & read(b))
        table |= read(row['output']) << assignment
    return table


def orbit(f):
    for order in permutations(range(4)):
        rows = [sum(((x >> i) & 1) << j for i, j in enumerate(order)) for x in range(16)]
        for phase in range(16):
            g = sum(((f >> (source ^ phase)) & 1) << x for x, source in enumerate(rows))
            yield g
            yield g ^ 0xffff


def target_certificate(exact3):
    target = 0x07e1
    excluded_by_absorption = 0
    excluded_by_identification = []
    for i, j in combinations(range(4), 2):
        for a, b in PHASES:
            fi = cofactor1(4, target, i, a)
            fj = cofactor1(4, target, j, b)
            from_i = exact3[fi] + 2 + (i in support(3, fj))
            from_j = exact3[fj] + 2 + (j - 1 in support(3, fi))
            if max(from_i, from_j) >= 7:
                excluded_by_absorption += 1
            else:
                g = identify(4, target, i, j, 1 ^ a ^ b)
                assert exact3[g] + 2 >= 7
                excluded_by_identification.append((i, j, a, b, hex(g), exact3[g]))
    assert excluded_by_absorption == 23 and len(excluded_by_identification) == 1
    print(json.dumps(dict(absorption_exclusions=excluded_by_absorption,
                          identification_exclusions=excluded_by_identification)), flush=True)


def main():
    small = {n: brute(n, limit, 'free') for n, limit in ((2, 3), (3, 6))}
    for n, costs in small.items():
        costs[0] = costs[(1 << (1 << n)) - 1] = 0
        assert len(costs) == 1 << (1 << n)
    target_certificate(small[3])
    library = json.loads((ROOT / 'results/cofactor_witness/npn4_witnesses.json').read_text())
    representative = {}
    for row in library:
        f = int(row['target'], 16)
        assert evaluate(row, 4) == f
        images = set(orbit(f))
        assert not representative.keys() & images
        representative.update(dict.fromkeys(images, f))
    assert len(representative) == 65536 and len(library) == 222
    upper = {int(row['target'], 16): len(row['gates']) for row in library}
    four = sorted(f for f in upper if len(support(4, f)) == 4)
    rng = Random(889)
    five = [rng.getrandbits(32) for _ in range(300)]
    rng = Random(886)
    six = [rng.getrandbits(64) for _ in range(80)]
    corpus = []
    for stem in ('synthesis_cases', 'synthesis_signed_cases'):
        for row in json.loads((ROOT / 'results' / (stem + '.json')).read_text()):
            n, known, f = (int(row[key]) for key in ('n', 'known', 'truth'))
            if known == (1 << (1 << n)) - 1:
                m, g = trim(n, f)
                if 2 <= m <= 7:
                    corpus.append((m, g))
    cases = {'npn4': [(4, f) for f in four], 'random5': [(5, f) for f in five],
             'random6': [(6, f) for f in six], 'corpus_up_to_7': corpus}
    raw = recurrence(None)
    assert all(raw(n, f) == _lower(*trim(n, f), 2) for n, f in cases['npn4'])
    modes = ('baseline', 'absorbing', 'profiles', 'phases')
    for regional in (False, True):
        for sample, targets in cases.items():
            # Keep the expensive recursive regional benchmark bounded.
            if regional and sample == 'random6':
                targets = targets[:16]
            values = {}
            elapsed = {}
            for mode in modes:
                for func in (identify, support, trim, cofactor1, subs):
                    func.cache_clear()
                lower = recurrence(small, regional, mode)
                start = perf_counter()
                values[mode] = [lower(n, f) for n, f in targets]
                elapsed[mode] = round(perf_counter() - start, 6)
            base = values['baseline']
            assert all(a <= b <= c <= d for a, b, c, d in zip(*(values[m] for m in modes)))
            report = dict(sample=sample, cases=len(targets), regional=regional, seconds=elapsed,
                          gains={m: sum(v > b for v, b in zip(values[m], base)) for m in modes},
                          incremental={m: sum(v > b for v, b in zip(values[m], values[p]))
                                       for p, m in zip(modes, modes[1:])},
                          examples={m: [hex(f) for (_, f), v, b in zip(targets, values[m], base) if v > b][:8]
                                    for m in modes if m != 'baseline'})
            if sample == 'npn4':
                for mode in modes:
                    assert all(v <= upper[f] for v, (_, f) in zip(values[mode], targets))
                target = four.index(0x07e1)
                report['07e1'] = {m: values[m][target] for m in modes}
                report['skip_witness_minus_one'] = {m: sum(v == upper[f] for v, (_, f) in zip(values[m], targets))
                                                     for m in modes}
                report['orbit_07e1'] = len(set(orbit(0x07e1)))
                assert report['07e1']['absorbing'] == upper[0x07e1] == 7
                if not regional:
                    assert report['07e1']['baseline'] == 6
            print(json.dumps(report), flush=True)
    m, f, k = strip_xor(4, 0x07e1)
    assert (m, f, k) == (4, 0x07e1, 0)
    witness = next(row for row in library if row['target'] == '07e1')
    print(json.dumps(dict(target='07e1', witness=witness, verified_rows=16, archived_witnesses=len(library))), flush=True)


if __name__ == '__main__':
    main()
