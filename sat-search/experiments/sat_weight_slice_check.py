"""Finite replay for the constant-weight SAT projection and slice compiler."""
import json
import subprocess
import sys
from itertools import combinations, permutations
from pathlib import Path
from random import Random

from sat_encoding_bound_review import encode, parse, satisfiable

ROOT = Path(__file__).resolve().parents[2]
HANDOFF = '26d92ea1ac4f97d26f729de93f8560107a4b008b'


def project(word):
    """Replace the final token by 00 and balance each other bit in a long identifier."""
    assert len(word) >= 2 and len(word) % 2 == 0
    payload = ''.join('10' if bit == '1' else '11' for bit in word[:-2])
    return word[:-2] + '00' + '10011101' + '10' + payload + '110100'


def check_projection(word):
    n = len(word)
    output = project(word)
    assert len(output) == 3 * n + 12 and output.count('1') == 2 * n + 5
    prefix = parse(word[:-2] + '00')
    result = parse(output)
    assert (result is None) == (prefix is None)
    if prefix is not None:
        assert result[:-1] == prefix
        assert result[-1][:2] == ((0, False), (0, True))
        expected_identifier = (1 << (n - 2)) | sum((bit == '0') << i for i, bit in enumerate(word[:-2]))
        assert result[-1][2] == (expected_identifier, False)
        assert len(result[-1]) == 3
    answer = satisfiable(parse(word))
    recovered = word.endswith('00') and satisfiable(result)
    assert recovered == answer
    return answer


def bitonic(size):
    """Comparators represented as (index of high output, index of low output)."""
    steps = []
    span = 2
    while span <= size:
        offset = span // 2
        while offset:
            for left in range(size):
                right = left ^ offset
                if left < right:
                    steps.append((right, left) if left & span else (left, right))
            offset //= 2
        span *= 2
    return steps


class MonotoneCircuit:
    def __init__(self, n):
        self.n = n
        self.gates = []

    def gate(self, op, left, right):
        self.gates.append((op, left, right))
        return self.n + 1 + len(self.gates)

    def evaluate(self, inputs, mask):
        values = [0, mask] + inputs
        for op, left, right in self.gates:
            a, b = values[left], values[right]
            values.append(a & b if op == 'and' else a | b)
        return values


def guarded_slice(n, weight, aig, out):
    """AIG literals use node 0 for the constant and bit 0 for edge phase."""
    circuit = MonotoneCircuit(n)
    forward = list(range(2, n + 2))
    size = 1 << (n - 1).bit_length()
    forward.extend([0] * (size - n))
    tape = []
    for hi, lo in bitonic(size):
        a, b = forward[hi], forward[lo]
        tape.append((hi, lo, a, b))
        forward[hi] = circuit.gate('or', a, b)
        forward[lo] = circuit.gate('and', a, b)
    negative = [int(i >= weight) for i in range(size)]
    for hi, lo, a, b in reversed(tape):
        not_hi, not_lo = negative[hi], negative[lo]
        negative[hi] = circuit.gate('or', not_hi, circuit.gate('and', b, not_lo))
        negative[lo] = circuit.gate('or', not_hi, circuit.gate('and', a, not_lo))
    rails = [(0, 1)] + [(i + 2, negative[i]) for i in range(n)]

    def read(literal):
        return rails[literal // 2][literal & 1]

    for a, b in aig:
        yes = circuit.gate('and', read(a), read(b))
        no = circuit.gate('or', read(a ^ 1), read(b ^ 1))
        rails.append((yes, no))
    ge = forward[weight - 1] if weight else 1
    gt = forward[weight] if weight < n else 0
    result = circuit.gate('or', gt, circuit.gate('and', ge, read(out)))
    assert len(circuit.gates) == 6 * len(tape) + 2 * len(aig) + 2
    return circuit, result, forward, negative


def check_compiler(rng):
    gate_rows = inversion_rows = guard_rows = 0
    for n in range(1, 11):
        rows = 1 << n
        mask = (1 << rows) - 1
        inputs = [sum(((row >> bit) & 1) << row for row in range(rows)) for bit in range(n)]
        slices = [0] * (n + 1)
        for row in range(rows):
            slices[row.bit_count()] |= 1 << row
        for _ in range(6):
            aig = [tuple(rng.randrange(2 * (n + i + 1)) for _ in range(2)) for i in range(2 * n)]
            out = rng.randrange(2 * (n + 1 + len(aig)))
            table = 0
            for row in range(rows):
                vals = [0] + [row >> i & 1 for i in range(n)]
                for a, b in aig:
                    vals.append((vals[a // 2] ^ (a & 1)) & (vals[b // 2] ^ (b & 1)))
                table |= (vals[out // 2] ^ (out & 1)) << row
            for weight, care in enumerate(slices):
                circuit, output, sorted_wires, negative = guarded_slice(n, weight, aig, out)
                vals = circuit.evaluate(inputs, mask)
                above = 0
                for stripe in slices[weight + 1:]:
                    above |= stripe
                assert vals[output] == above | (table & care)
                threshold = mask
                for i, sorted_wire in enumerate(sorted_wires):
                    if i <= n:
                        threshold ^= slices[i]
                    assert vals[sorted_wire] == threshold
                for i in range(n):
                    assert (vals[negative[i]] ^ inputs[i]) & care == care
                guard_rows += rows
                inversion_rows += n * care.bit_count()
                gate_rows += len(circuit.gates) * rows
    return dict(guard_rows=guard_rows, inversion_rows=inversion_rows, gate_rows=gate_rows)


def check_orbit_barrier():
    """Average all vertex relabelings using heterogeneous edge weights."""
    checks = 0
    for n in range(4, 8):
        all_edges = list(combinations(range(n), 2))
        weights = {edge: 1 + 3 * i * i for i, edge in enumerate(all_edges)}
        total_weight = sum(weights.values())
        for k in range(3, n):
            positive = list(combinations(range(k), 2))
            negative = [edge for edge in combinations(range(k + 1), 2) if edge not in ((0, 1), (2, 3))]
            assert not any(all(edge in negative for edge in combinations(part, 2))
                           for part in combinations(range(n), k))
            yes = no = labels = 0
            for perm in permutations(range(n)):
                yes += sum(weights[tuple(sorted((perm[i], perm[j])))] for i, j in positive)
                no += sum(weights[tuple(sorted((perm[i], perm[j])))] for i, j in negative)
                labels += 1
            denominator = len(all_edges)
            assert yes * denominator == labels * total_weight * len(positive)
            assert no * denominator == labels * total_weight * len(negative)
            assert no > yes
            checks += labels
    return checks


def main():
    rng = Random(261126)
    exhaustive = positives = seeded = 0
    for n in range(2, 15, 2):
        for value in range(1 << n):
            positives += check_projection(f'{value:0{n}b}')
            exhaustive += 1
    seeded_positives = 0
    for _ in range(1000):
        cnf = [[(rng.randrange(6), bool(rng.randrange(2))) for _ in range(rng.randrange(4))]
               for _ in range(rng.randint(1, 8))]
        word = encode(cnf)
        assert parse(word) == tuple(tuple(clause) for clause in cnf)
        seeded_positives += check_projection(word)
        offset = rng.randrange(len(word))
        damaged = word[:offset] + str(1 - int(word[offset])) + word[offset + 1:]
        seeded_positives += check_projection(damaged)
        seeded += 2
    print(json.dumps(dict(exhaustive_projection_rows=exhaustive, positives=positives,
                          seeded_projection_rows=seeded, seeded_positives=seeded_positives,
                          clique_vertex_relabelings=check_orbit_barrier(), **check_compiler(rng))), flush=True)


def replay_handoff():
    blob = subprocess.check_output(['git', 'show', HANDOFF + ':sat-search/chatgpt_handoff/README.md'], cwd=ROOT)
    fence = chr(96) * 3
    code = blob.decode('utf-8').split(fence + 'python', 1)[1].split(fence, 1)[0]
    subprocess.run([sys.executable, '-B', '-c', code], cwd=ROOT, check=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['--replay-handoff']:
        replay_handoff()
    else:
        assert not sys.argv[1:]
        main()
