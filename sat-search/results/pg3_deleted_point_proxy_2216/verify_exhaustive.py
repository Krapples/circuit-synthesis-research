"""Exhaustively verify the 25-input, two-output PG(2,3) construction."""
import json
from pathlib import Path
from time import perf_counter


def low_columns(bits):
    width = 1 << (bits - 3)
    columns = [bytes([byte]) * width for byte in (0xAA, 0xCC, 0xF0)]
    for index in range(3, bits):
        period = (bytes(1 << (index - 3)) + bytes([0xFF]) * (1 << (index - 3)))
        columns.append(period * (width // len(period)))
    return [int.from_bytes(column, "little") for column in columns]


def verify():
    artifact = Path(__file__).with_name("L-meta-2216-upper62.json")
    data = json.loads(artifact.read_text(encoding="utf-8"))
    gates = data["gates"]
    graph_wire, proxy_wire = data["output"], data["proxy"]
    assert len(gates) == 62
    assert 0 <= graph_wire < 25 + len(gates)
    assert 0 <= proxy_wire < 25 + len(gates)
    for step, (op, a, b) in enumerate(gates, 25):
        assert op in (0, 1) and 0 <= a < step and 0 <= b < step

    edges = [(p, line) for p in range(12) for line in range(12, 25)
             if (p + line + 2) % 13 in (0, 1, 3, 9)]
    matching = [(p, next(q for q in range(12, 25) if (p + q + 2) % 13 == 0))
                for p in range(12)]
    assert len(edges) == 48 and len({q for _, q in matching}) == 12
    assert set(matching) <= set(edges)

    low = 20
    rows = 1 << low
    full = (1 << rows) - 1
    columns = low_columns(low)
    graph_true = 0
    graph_false_proxy_true = 0
    for high in range(1 << (25 - low)):
        inputs = columns + [full if high & (1 << i) else 0 for i in range(25 - low)]
        wires = inputs.copy()
        for op, a, b in gates:
            wires.append(wires[a] | wires[b] if op else wires[a] & wires[b])
        expected = 0
        for p, line in edges:
            expected |= inputs[p] & inputs[line]
        desired_proxy = inputs[12] | inputs[13] | inputs[15] | inputs[21]
        assert wires[graph_wire] == expected
        assert (wires[proxy_wire] ^ desired_proxy) & (full ^ expected) == 0
        graph_true += expected.bit_count()
        graph_false_proxy_true += (desired_proxy & (full ^ expected)).bit_count()

    summary = {
        "gates": len(gates),
        "rows": 1 << 25,
        "graph_true": graph_true,
        "graph_false": (1 << 25) - graph_true,
        "graph_false_proxy_true": graph_false_proxy_true,
    }
    return summary


if __name__ == "__main__":
    start = perf_counter()
    print(json.dumps(verify(), sort_keys=True))
    print(f"Wall time {perf_counter() - start:.3f} s")
