"""Replay the pinned Andreev handoff and check selector-only sharing independently."""

import random
import subprocess
import sys


def replay_handoff():
    path = "sat-search/chatgpt_handoff/README.md"
    revision = "822b44415b0ad68318fd98179a3eeb64bae9b7cd"
    blob = subprocess.check_output(["git", "show", f"{revision}:{path}"])
    code = blob.split(b"```python\n", 1)[1].split(b"```", 1)[0]
    checksum = 2166136261
    for byte in code:
        checksum = ((checksum ^ byte) * 16777619) & 0xffffffff
    assert (len(code), checksum) == (6918, 0x6b03f877)
    subprocess.run([sys.executable, "-B", "-c", code.decode("ascii")], check=True)


def build(k):
    data = 1 << k
    width = data // k
    primaries = data + k * width
    gates = []

    def gate(a, b):
        gates.append((a, b))
        return 2 * (primaries + len(gates) - 1)

    def xor(a, b):
        return gate(gate(a, b ^ 1) ^ 1, gate(a ^ 1, b) ^ 1) ^ 1

    def parity(lo, hi):
        if hi - lo == 1:
            return 2 * lo
        mid = (lo + hi) // 2
        return xor(parity(lo, mid), parity(mid, hi))

    address = [parity(data + j * width, data + (j + 1) * width) for j in range(k)]
    first_parity_gate = address[0] // 2
    mux_nodes = [2 * i for i in range(data)]
    for s in address:
        mux_nodes = [
            gate(gate(s ^ 1, lo) ^ 1, gate(s, hi) ^ 1) ^ 1
            for lo, hi in zip(mux_nodes[::2], mux_nodes[1::2])
        ]
    return data, width, primaries, gates, first_parity_gate, mux_nodes[0]


def sharing_check():
    rng = random.Random(822444)
    evaluations = 0
    for k in range(1, 13):
        data, width, primaries, gates, row_zero, output = build(k)
        data_ancestor = [True] * data + [False] * (primaries - data)
        for a, b in gates:
            data_ancestor.append(data_ancestor[a // 2] or data_ancestor[b // 2])

        paths = [0] * (primaries + len(gates))
        paths[output // 2] = 1
        for target, (a, b) in reversed(list(enumerate(gates, primaries))):
            paths[a // 2] += paths[target]
            paths[b // 2] += paths[target]

        assert len(gates) == 3 * (k * (width - 1) + data - 1)
        assert sum(data_ancestor[primaries:]) == 3 * (data - 1)
        assert all(p > 0 for p in paths[primaries:])
        assert all(paths[g] == 1 for g in range(primaries, len(paths)) if data_ancestor[g])
        assert paths[row_zero] == data
        assert max(paths[primaries:row_zero + 1]) >= data * (1 << (width.bit_length() - 2))

        rows = range(1 << primaries) if primaries <= 8 else (
            rng.getrandbits(primaries) for _ in range(32)
        )
        for x in rows:
            values = [(x >> i) & 1 for i in range(primaries)]
            for a, b in gates:
                values.append((values[a // 2] ^ (a & 1)) & (values[b // 2] ^ (b & 1)))
            index = sum(
                (((x >> (data + j * width)) & ((1 << width) - 1)).bit_count() % 2) << j
                for j in range(k)
            )
            assert values[output // 2] ^ (output & 1) == (x >> index) & 1
            evaluations += 1
        print(f"k={k} gates={len(gates)} leaves={1 + sum(paths[primaries:])} "
              f"max_path={max(paths[primaries:])} max_data_ancestor_path=1")
    print(f"selector-only sharing verified on {evaluations} circuit evaluations")


if __name__ == "__main__":
    replay_handoff()
    sharing_check()
