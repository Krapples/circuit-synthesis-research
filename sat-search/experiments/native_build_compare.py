"""Compare two native builds on the archived regional query corpus.

Usage: python -B sat-search/experiments/native_build_compare.py BASELINE_DIR CANDIDATE_DIR OUTPUT_JSONL
Each build directory contains the extension for the current Python ABI. Use a fresh output path.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def read_queries():
    results = ROOT / "results"
    decisions = {}
    with (results / "native_differential_captured.jsonl").open(encoding="utf-8") as stream:
        for line in stream:
            record = json.loads(line)
            decisions[record["source"], record["idx"]] = record
    for tag, suffix in (("heldout", "_heldout"), ("dev", "")):
        with (results / f"phase_first_captured{suffix}.jsonl").open(encoding="utf-8") as stream:
            for line in stream:
                record = json.loads(line)
                for index, query in enumerate(record["queries"]):
                    m, ports, patterns, targets = query[:4]
                    key = tag, f"{record['case']}:{record['kind']}:{index}"
                    yield m, tuple(ports), tuple(patterns), tuple(targets), decisions[key]


def measure(extension, check):
    sys.path.insert(0, str(extension.resolve()))
    import _regional_native
    assert Path(_regional_native.__file__).resolve().parent == extension.resolve()
    for folder in ("", "theory", "experiments"):
        sys.path.insert(0, str(ROOT / folder))
    from native_differential import peak_working_set_mb
    from regional_native import completion_native
    from regional_production_adapter import check_tree

    queries = list(read_queries())
    output = {}
    for mode, signed, adaptive in (("blocks_signed", True, False), ("blocks_mono", False, False),
                                   ("phase_first", True, True)):
        args = [(m, p, ps, ts, signed) for m, p, ps, ts, record in queries
                if record[mode]["py"] != "timeout" and record[mode]["native"] != "timeout"]
        digest = hashlib.sha256()
        statuses = Counter()
        if check:
            for query in args:
                stats = {}
                witness = completion_native(*query, adaptive=adaptive, native_stats=stats)
                assert stats, "unexpected fallback to the Python implementation"
                if witness is not None:
                    check_tree(witness, *query)
                statuses["sat" if witness is not None else "unsat"] += 1
                digest.update(repr((witness, sorted(stats.items()))).encode("utf-8"))
            output[mode] = dict(count=len(args), statuses=statuses, sha256=digest.hexdigest())
        else:
            start = time.perf_counter()
            for query in args:
                completion_native(*query, adaptive=adaptive)
            output[mode] = dict(count=len(args), seconds=time.perf_counter() - start)
    if not check:
        output["peak_mib"] = peak_working_set_mb()
    return output


if __name__ == "__main__":
    if sys.argv[1] in ("time", "check"):
        print(json.dumps(measure(Path(sys.argv[2]), sys.argv[1] == "check")))
    else:
        baseline, candidate, destination = sys.argv[1:4]
        with Path(destination).open("x", encoding="utf-8") as results:
            checks = (
                [("baseline", baseline), ("candidate", candidate)]
                + [("baseline", baseline), ("candidate", candidate), ("candidate", candidate), ("baseline", baseline)] * 2
            )
            observed = {}
            for index, (variant, extension) in enumerate(checks):
                mode = "check" if index < 2 else "time"
                completed = subprocess.run(
                    [sys.executable, "-B", __file__, mode, extension],
                    stdout=subprocess.PIPE, text=True, check=True, timeout=40,
                )
                result = json.loads(completed.stdout)
                if mode == "check":
                    observed[variant] = result
                record = dict(variant=variant, mode=mode, result=result)
                results.write(json.dumps(record) + "\n")
                results.flush()
        assert observed["baseline"] == observed["candidate"], observed
        print(json.dumps(observed["candidate"], sort_keys=True))
