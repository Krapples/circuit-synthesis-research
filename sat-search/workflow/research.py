"""Entry point for the repository's reusable research workflow."""

import argparse
from contextlib import closing
import ctypes
import json
import os
from pathlib import Path
import sys
import time

from common import ROOT, excerpt, read_json, write_json
from graph import canonical_graph
from ops import heartbeat, lean_command, normalize, checkpoint, pr_status, selected_paths, stamp
from runs import DEFAULT_WORKERS, build_jobs, connect, finite_number, recover, run_batch


def available_memory():
    if os.name == "nt":
        class Memory(ctypes.Structure):
            _fields_ = [("length", ctypes.c_uint32), ("load", ctypes.c_uint32)] + [
                (name, ctypes.c_uint64) for name in ("total_phys", "free_phys", "total_page", "free_page",
                                                      "total_virtual", "free_virtual", "free_extended")]
        info = Memory()
        info.length = ctypes.sizeof(info)
        if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(info)):
            return int(0.7 * info.free_phys / (2 ** 20))
    elif Path("/proc/meminfo").is_file():
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemAvailable:"):
                return int(0.7 * int(line.split()[1]) / 1024)
    return 512 * DEFAULT_WORKERS


def cpu_slots():
    count = getattr(os, "process_cpu_count", os.cpu_count)() or 1
    return min(DEFAULT_WORKERS, count)


def emit(record):
    print(json.dumps(record, ensure_ascii=False), flush=True)


def status(state, task=None):
    with closing(connect(state)) as db:
        runs = [dict(r) for r in db.execute("SELECT status, COUNT(*) AS count, ROUND(SUM(seconds),3) AS seconds "
                                            "FROM attempts GROUP BY status ORDER BY status")]
        skips = [dict(r) for r in db.execute("SELECT reason, COUNT(*) AS count FROM skips GROUP BY reason ORDER BY reason")]
        active = [dict(r) for r in db.execute("SELECT number,name,pid,host,started,cap,folder FROM attempts "
                                              "WHERE status='running' ORDER BY number")]
    ledger = state / "ledger"
    progress = []
    if task is not None:
        for path in sorted(ledger.glob("*.json"), reverse=True):
            event = read_json(path)
            if event["task"] == task:
                progress.append(event)
                if len(progress) == 10:
                    break
    else:
        progress = [read_json(path) for path in sorted(ledger.glob("*.json"), reverse=True)[:10]]
    desk = state / "desk"
    pull_requests = [{k: item[k] for k in ("at", "number", "state", "merged", "url")}
                     for p in sorted(desk.glob("*.json"), key=lambda f: f.stat().st_mtime, reverse=True)[:8]
                     if (item := read_json(p)).get("number")]
    heartbeats = []
    paths = [desk / f"{task}.jsonl"] if task and Path(task).name == task and task not in {".", ".."} else []
    if task is None:
        paths = sorted(desk.glob("*.jsonl"), key=lambda f: f.stat().st_mtime, reverse=True)[:8]
    for path in paths:
        if path.is_file() and (lines := excerpt(path).splitlines()):
            heartbeats.append(json.loads(lines[-1]))
    return {"runs": runs, "skips": skips, "running": active, "recent_progress": progress,
            "recent_prs": pull_requests, "recent_heartbeats": heartbeats}


def add_record(state, args):
    event = {"schema": "research-progress/1", "at": stamp(), "task": args.task, "kind": args.kind,
             "summary": args.summary, "scope": args.scope, "open": args.open_obligation,
             "artifacts": args.artifact, "next": args.next, "active_jobs": args.job,
             "lease_state": args.lease_state, "metrics": read_json(args.metrics) if args.metrics else None}
    destination = state / "ledger" / f"{time.time_ns()}-{os.getpid()}.json"
    write_json(destination, event)
    emit({"record": str(destination), **event})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state-dir", type=Path, default=ROOT / ".research")
    sub = parser.add_subparsers(dest="action", required=True)

    run = sub.add_parser("run", help="run or resume a research batch")
    run.add_argument("batch", type=Path)
    run.add_argument("--workers", type=int, default=cpu_slots())
    run.add_argument("--memory-mib", type=int, default=None)
    run.add_argument("--repeat-reason", help="log why a completed query should run again")
    run.add_argument("--verbose", action="store_true", help="also emit per-job records")
    status_parser = sub.add_parser("status", help="show active jobs, duplicate counts, and recent research progress")
    status_parser.add_argument("--task")
    recovery = sub.add_parser("recover", help="retire a reservation after its recorded processes exit")
    recovery.add_argument("number", type=int)
    recovery.add_argument("--reason", required=True)

    canon = sub.add_parser("canonicalize", help="canonicalize a simple graph JSON object")
    canon.add_argument("graph", type=Path)
    canon.add_argument("--limit", type=int, default=20_000)

    record = sub.add_parser("record", help="append a structured research milestone")
    record.add_argument("--task", required=True)
    record.add_argument("--kind", required=True, choices=["hypothesis", "analytical", "lean_checked", "verified_witness",
                                                          "solver_verdict", "open", "submitted", "lease", "workflow"])
    record.add_argument("--summary", required=True)
    record.add_argument("--scope", help="target, basis, budget and any restrictions")
    record.add_argument("--open-obligation")
    record.add_argument("--artifact", action="append", default=[])
    record.add_argument("--job", action="append", default=[])
    record.add_argument("--lease-state", help="redacted status and expiry only")
    record.add_argument("--metrics", type=Path, help="optional JSON file containing measured research effort")
    record.add_argument("--next")

    text = sub.add_parser("normalize", help="rewrite explicitly selected text files as UTF-8 LF")
    text.add_argument("paths", nargs="+")
    git = sub.add_parser("checkpoint", help="normalize, stage, and record the diff of explicitly selected files")
    git.add_argument("--message", help="also make a focused local commit")
    git.add_argument("paths", nargs="+")

    lease = sub.add_parser("heartbeat", help="renew a privately stored project lease")
    lease.add_argument("lease_file", type=Path)
    lease.add_argument("--seconds", type=int, default=240)
    lease.add_argument("--once", action="store_true")
    pull = sub.add_parser("pr", help="record a PR status or watch it until it closes")
    pull.add_argument("number", type=int)
    pull.add_argument("--watch", action="store_true")
    pull.add_argument("--interval", type=int, default=60)

    lean = sub.add_parser("lean", help="use the project's locked, incremental Lake environment")
    lean.add_argument("workspace", type=Path)
    choice = lean.add_mutually_exclusive_group(required=True)
    choice.add_argument("--module")
    choice.add_argument("--source", type=Path)
    lean.add_argument("--lake")
    lean.add_argument("--timeout", type=float, default=300)

    args = parser.parse_args()
    state = args.state_dir.resolve()
    if args.action == "run":
        workers = args.workers
        memory = available_memory() if args.memory_mib is None else args.memory_mib
        if workers < 1 or memory < 1 or args.repeat_reason is not None and not args.repeat_reason.strip():
            raise ValueError("positive resources and a nonblank repeat reason are required")
        manifest = read_json(args.batch)
        jobs = build_jobs(manifest, min(DEFAULT_WORKERS, workers))
        batch = state / "batches" / f"{time.time_ns()}-{os.getpid()}"
        batch.mkdir(parents=True)
        write_json(batch / "request.json", {"manifest": str(args.batch.resolve()), "at": stamp(), "workers": workers,
                   "memory_mib": memory, "repeat_reason": args.repeat_reason, "decision": manifest.get("decision"),
                   "jobs": [{"id": j.name, "key": j.key, "spec": j.spec} for j in jobs]})

        failures = []
        def report(record):
            with (batch / "jobs.jsonl").open("a", encoding="utf-8", newline="\n") as log:
                log.write(json.dumps(record) + "\n")
            short = {k: record[k] for k in ("name", "status", "number", "cap", "seconds", "folder", "previous", "excerpt")
                     if k in record}
            if args.verbose:
                emit(short)
            if record["status"] in {"error", "evidence_missing"} and len(failures) < 3:
                failures.append(short)

        summary = run_batch(state, jobs, workers, memory, args.repeat_reason, report)
        write_json(batch / "summary.json", {**summary, "actionable": failures})
        summary["actionable"] = failures
        emit({"batch": str(batch), **summary})
        return 130 if summary["interrupted"] else int(bool(failures))
    if args.action == "status":
        emit(status(state, args.task))
    elif args.action == "recover":
        if not args.reason.strip():
            raise ValueError("recovery requires a nonblank reason")
        emit(recover(state, args.number, args.reason))
    elif args.action == "canonicalize":
        graph = read_json(args.graph)
        canonical = canonical_graph(graph["n"], graph["edges"], colors=graph.get("colors"), limit=args.limit)
        emit(vars(canonical))
    elif args.action == "record":
        add_record(state, args)
    elif args.action == "normalize":
        emit({"normalized": normalize(selected_paths(args.paths))})
    elif args.action == "checkpoint":
        emit(checkpoint(state, selected_paths(args.paths), args.message))
    elif args.action == "heartbeat":
        event = heartbeat(state, args.lease_file.resolve(), args.seconds, args.once)
        emit(event)
        return int(event["status"] not in {"renewed", "local_stop"})
    elif args.action == "pr":
        if args.interval < 15:
            raise ValueError("PR polls must be at least 15 seconds apart")
        previous = None
        while True:
            result = pr_status(state, args.number)
            signature = (result["state"], result["merged"], result["head"], result["bot_verdicts"])
            if signature != previous:
                emit(result)
            if not args.watch or result["state"] != "open":
                break
            previous = signature
            time.sleep(args.interval)
    else:
        finite_number(args.timeout, "Lean timeout", 0.01)
        result = lean_command(state, args.workspace, args.module, args.source, args.timeout, args.lake)
        emit(result)
        return int(result["status"] != "ok")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as ex:
        emit({"error": str(ex)[:1800]})
        sys.exit(1)
    except KeyboardInterrupt:
        sys.exit(130)
