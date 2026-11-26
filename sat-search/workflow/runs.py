"""Resource-bounded research batches and an evidence-aware run database."""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import closing
from dataclasses import dataclass
from importlib.machinery import PathFinder
import math
import os
from pathlib import Path
import platform
import shutil
import socket
import sqlite3
import sys
from threading import Event
import time

from common import ROOT, SAT, digest, excerpt, file_hash, process_alive, read_json, run_logged, write_json
from graph import canonical_graph


TERMINAL = {"command_ok", "verified_sat", "solver_unsat"}
DUPLICATES = {"cache_hit", "already_running", "already_attempted"}
SKIPPED = DUPLICATES | {"timeout_ceiling", "evidence_missing"}
CUBE_SOURCES = ("cube_search.py", "partial_ordered.py", "monotone_interface.py", "port_certificates.py",
                "provider_certificates.py", "provider_capacity.py", "rulesets.py", "verify/manifest.py",
                "verify/reference.py", "verified_combinations.json")
DEFAULT_WORKERS = 22
ADAPTER_VERSION = "research-adapters/1"


@dataclass(frozen=True)
class Job:
    name: str
    kind: str
    cwd: Path
    argv: tuple[str, ...]
    key: str
    spec: dict
    schedule: tuple[float, float, float]
    slots: int
    memory: int
    cache: bool


def finite_number(value, name, minimum):
    if type(value) not in (int, float) or not math.isfinite(value) or value < minimum:
        raise ValueError(f"{name} must be finite and at least {minimum}")
    return float(value)


def sat_runtime():
    lookup = [*sys.path, str(ROOT / ".scratch-sat")]
    result = {}
    for mod in ("pysat", "pysolvers", "pycard", "pyformula"):
        spec = PathFinder.find_spec(mod, lookup)
        if spec and spec.origin and Path(spec.origin).is_file():
            path = Path(spec.origin)
            result[mod] = {path.name: file_hash(path)}
            if spec.submodule_search_locations:
                result[mod].update({str(p.relative_to(path.parent)): file_hash(p) for p in path.parent.rglob("*.py")})
    if "pysolvers" not in result:
        raise ValueError("compiled python-sat backend unavailable for this interpreter")
    return result


def build_jobs(batch, default_workers=DEFAULT_WORKERS):
    if batch.get("schema") != "research-batch/1" or not isinstance(batch.get("jobs"), list):
        raise ValueError("expected research-batch/1 with a jobs list")
    jobs = []
    runtime = None
    for entry in batch["jobs"]:
        name = entry["id"]
        if not isinstance(name, str) or not name.strip():
            raise ValueError("every job needs a nonempty id")
        kind = entry.get("kind", "command")
        slots = entry.get("workers", default_workers if kind == "cube" else 1)
        memory = entry.get("memory_mib", 512 * slots)
        if type(slots) is not int or slots < 1 or type(memory) is not int or memory < 1:
            raise ValueError(f"{name}: positive integer workers and memory_mib required")
        policy = entry.get("timeout", {})
        initial = finite_number(policy.get("initial", 60), "initial timeout", 0.01)
        ceiling = finite_number(policy.get("maximum", initial), "maximum timeout", initial)
        factor = finite_number(policy.get("factor", 2), "timeout multiplier", 1.01)
        sources = [(ROOT / p).resolve() for p in entry.get("inputs", [])]
        cwd = (ROOT / entry.get("cwd", ".")).resolve()
        query = dict(entry.get("query", {}))
        cache = bool(entry.get("cache", kind == "cube"))
        if kind == "cube":
            if set(query) - {"n", "edges", "size", "basis", "solver", "symmetry"}:
                raise ValueError(f"{name}: pinned or specialized scopes require an explicit command job")
            if sources or "argv" in entry:
                raise ValueError(f"{name}: cube adapter chooses its own command and verified sources")
            graph = canonical_graph(query["n"], query["edges"])
            size, basis = query["size"], query.get("basis", "monotone")
            if not graph.edges or type(size) is not int or size < 1 or basis not in {"general", "monotone"}:
                raise ValueError(f"{name}: invalid graph, gate budget or basis")
            if len({v for e in graph.edges for v in e}) != graph.n:
                raise ValueError(f"{name}: cube exact-size model requires every input to be essential")
            solver = query.get("solver", "maplechrono")
            argv = [sys.executable, "-B", str(SAT / "cube_search.py"), "--n", str(graph.n), "--edges", graph.argument(),
                    "--size", str(size), "--solver", solver, "--workers", str(slots)]
            if basis == "monotone":
                argv.append("--monotone")
            if query.get("symmetry", False):
                argv.append("--symmetry")
            identity = {"model": "exact-G", "n": graph.n, "edges": graph.edges, "size": size, "basis": basis,
                        "solver": solver, "symmetry": bool(query.get("symmetry", False)), "canonical": graph.canonical}
            spec = {**identity, "original_edges": query["edges"], "original_to_run": graph.old_to_new}
            sources = [SAT / p for p in CUBE_SOURCES]
            runtime = sat_runtime() if runtime is None else runtime
        elif kind == "command":
            argv = entry["argv"]
            if not isinstance(argv, list) or not argv or not all(isinstance(v, str) and v for v in argv):
                raise ValueError(f"{name}: argv must be a nonempty list of strings")
            if cache and not sources:
                raise ValueError(f"{name}: a cacheable command must declare its source and input files")
            identity = spec = query
        else:
            raise ValueError(f"{name}: unknown kind {kind!r}")
        executable = shutil.which(argv[0])
        executable_id = [(str(executable), file_hash(executable))] if executable else [(argv[0], None)]
        hashes = {str(p): file_hash(p) for p in sources}
        key_argv = argv[:argv.index("--workers")] + argv[argv.index("--workers") + 2:] if kind == "cube" else argv
        key = digest({"kind": kind, "cwd": str(cwd), "argv": key_argv, "exe": executable_id, "query": identity,
                      "files": hashes, "implementation": ADAPTER_VERSION, "platform": platform.platform(),
                      "python": sys.version, "solver_sources": runtime if kind == "cube" else None,
                      "argv_environment": {k: os.environ.get(k) for k in sorted(entry.get("environment_keys", []))}})
        jobs.append(Job(name, kind, cwd, tuple(argv), key, {"query": spec, "sources": hashes},
                        (initial, ceiling, factor), slots, memory, cache))
    if len({j.name for j in jobs}) != len(jobs):
        raise ValueError("job ids must be unique within a batch")
    return jobs


def connect(state):
    state.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(state / "runs.sqlite3", timeout=20)
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA journal_mode=WAL")
    db.executescript("""
        CREATE TABLE IF NOT EXISTS attempts (
            number INTEGER PRIMARY KEY, key TEXT NOT NULL, name TEXT NOT NULL, status TEXT NOT NULL,
            host TEXT NOT NULL, pid INTEGER NOT NULL, started REAL NOT NULL, finished REAL,
            cap REAL NOT NULL, seconds REAL, reason TEXT, folder TEXT,
            slots INTEGER NOT NULL, memory INTEGER NOT NULL, result_hash TEXT
        );
        CREATE UNIQUE INDEX IF NOT EXISTS active_key ON attempts(key) WHERE status='running';
        CREATE INDEX IF NOT EXISTS history_key ON attempts(key, number);
        CREATE TABLE IF NOT EXISTS skips (key TEXT NOT NULL, name TEXT NOT NULL, reason TEXT NOT NULL, at REAL NOT NULL);
    """)
    return db


def reusable_artifacts(row, kind):
    folder = Path(row["folder"])
    result = folder / "result.json"
    try:
        if file_hash(result) != row["result_hash"] or not (folder / "stdout.log").is_file() or not (folder / "stderr.log").is_file():
            return False
        return kind != "cube" or (file_hash(folder / "evidence.json") == read_json(result)["evidence"]["sha256"]
                                  and (folder / "verify/stdout.log").is_file())
    except (OSError, ValueError, KeyError):
        return False


def recover(state, number, reason):
    with closing(connect(state)) as db, db:
        db.execute("BEGIN IMMEDIATE")
        row = db.execute("SELECT * FROM attempts WHERE number=? AND status='running'", (number,)).fetchone()
        if row is None:
            raise ValueError(f"no running attempt {number}")
        if row["host"] != socket.gethostname() or process_alive(row["pid"]):
            raise ValueError(f"attempt {number} must be recovered on its host after its runner exits")
        folder = Path(row["folder"])
        for path in (folder / "process.json", folder / "verify/process.json"):
            if path.is_file() and process_alive(read_json(path)["pid"]):
                raise ValueError(f"attempt {number} still has a live recorded process")
        record = {"number": number, "status": "interrupted", "reason": reason,
                  "previous_reason": row["reason"], "folder": str(folder), "at": time.time()}
        write_json(folder / "recovery.json", record)
        db.execute("UPDATE attempts SET status='interrupted', finished=? WHERE number=?", (record["at"], number))
    return record


def reserve(db, state, job, repeat_reason, repeat_before, workers, memory):
    with db:
        db.execute("BEGIN IMMEDIATE")
        existing = db.execute("SELECT * FROM attempts WHERE key=? ORDER BY number DESC", (job.key,)).fetchall()
        last = existing[0] if existing else None
        completed = next((r for r in existing if r["status"] in TERMINAL), None)
        reusable = next((r for r in existing if r["status"] in TERMINAL and reusable_artifacts(r, job.kind)), None)
        if last and last["number"] > repeat_before:
            repeat_reason = None
        initial, ceiling, factor = job.schedule
        cap = initial
        reason = None
        cap_reason = repeat_reason
        if last and last["status"] == "running":
            reason, source = "already_running", last
        elif job.cache and reusable and not repeat_reason:
            reason, source = "cache_hit", reusable
        elif job.cache and completed and not repeat_reason:
            reason, source = "evidence_missing", completed
        elif job.cache and last and last["number"] > repeat_before:
            reason, source = "already_attempted", last
        elif last and last["status"] in {"timeout", "open"}:
            cap = min(ceiling, max(initial, last["cap"] * factor))
            if cap <= last["cap"] and not repeat_reason:
                reason, source = "timeout_ceiling", last
            elif cap > last["cap"] and not cap_reason:
                cap_reason = f"adaptive retry after attempt {last['number']} left open at {last['cap']:g}s"
        if reason:
            db.execute("INSERT INTO skips VALUES(?,?,?,?)", (job.key, job.name, reason, time.time()))
            return None, {"name": job.name, "status": reason, "key": job.key, "previous": source["folder"],
                          "query": job.spec["query"]}
        host = socket.gethostname()
        used = db.execute("SELECT COALESCE(SUM(slots),0), COALESCE(SUM(memory),0) FROM attempts "
                          "WHERE status='running' AND host=?", (host,)).fetchone()
        if used[0] + job.slots > workers or used[1] + job.memory > memory:
            return None, None
        cursor = db.execute("INSERT INTO attempts(key,name,status,host,pid,started,cap,reason,slots,memory) "
                            "VALUES(?,?,?,?,?,?,?,?,?,?)",
                            (job.key, job.name, "running", host, os.getpid(), time.time(), cap, cap_reason, job.slots, job.memory))
        number = cursor.lastrowid
        folder = state / "runs" / f"{number:06d}-{job.key[:12]}"
        db.execute("UPDATE attempts SET folder=? WHERE number=?", (str(folder), number))
        return (number, cap, folder, cap_reason), None


def evaluate(job, reservation, cancel):
    number, cap, folder, cap_reason = reservation
    folder.mkdir(parents=True, exist_ok=False)
    argv = list(job.argv)
    environment = os.environ.copy()
    stop = None
    if job.kind == "cube":
        stop = folder / "STOP"
        environment["CUBE_SEARCH_STOP_FILE"] = str(stop)
        argv += ["--manifest", str(folder / "evidence.json")]
    write_json(folder / "request.json", {"number": number, "name": job.name, "argv": argv, "cwd": str(job.cwd),
               "key": job.key, "timeout": cap, "workers": job.slots, "memory_mib": job.memory,
               "run_reason": cap_reason, **job.spec})
    result = run_logged(argv, job.cwd, folder, cap, env=environment, stop=stop, cancel=cancel)
    status = "interrupted" if result["interrupted"] else "timeout" if result["timeout"] else "error"
    evidence = {"kind": "none"}
    solver_seconds = 0.0
    if not result["timeout"] and not result["interrupted"] and result["returncode"] == 0:
        if job.kind == "command":
            status = "command_ok"
        elif (folder / "evidence.json").is_file():
            manifest = read_json(folder / "evidence.json")
            solver_seconds = round(sum(c["seconds"] for c in manifest["cubes"]), 6)
            if manifest["result"] == "STOPPED":
                status = "open"
            else:
                verification = run_logged([sys.executable, "-B", str(SAT / "verify/manifest.py"),
                                           str(folder / "evidence.json")], job.cwd, folder / "verify", max(30, cap), cancel=cancel)
                result["verify"] = verification
                if verification["interrupted"]:
                    status = "interrupted"
                elif verification["timeout"]:
                    status = "open"
                elif verification["returncode"] == 0:
                    report = read_json(verification["stdout"])
                    desired = job.spec["query"]
                    profile = manifest["model"]
                    target = manifest["target"]
                    scope_matches = (target["n"] == desired["n"] and tuple(map(tuple, target["edges"])) == desired["edges"]
                                     and profile["size"] == desired["size"] and profile["basis"] == desired["basis"]
                                     and not profile["pinned_prefix"] and profile["kind"] == "exact-G")
                    if scope_matches and report["sources_match"]:
                        if report["grade"] == "sat" and manifest["result"] == "WITNESS":
                            status = "verified_sat"
                        if report["grade"] == "rule-dependent" and manifest["result"] == "ALL UNSAT" and manifest["coverage"]["complete"]:
                            status = "solver_unsat"
                    evidence = {"kind": report["grade"], "scope_matches": scope_matches,
                                "sha256": file_hash(folder / "evidence.json")}
    result.update(name=job.name, key=job.key, status=status, number=number, cap=cap, folder=str(folder),
                  seconds=round(result["seconds"] + result.get("verify", {}).get("seconds", 0), 6),
                  solver_job_seconds=solver_seconds, evidence=evidence)
    write_json(folder / "result.json", result)
    if status == "error":
        failed = result.get("verify", result)
        result["excerpt"] = excerpt(failed["stderr"]) or excerpt(failed["stdout"])
    return result


def run_batch(state, jobs, workers, memory, repeat_reason, report):
    if any(j.slots > workers or j.memory > memory for j in jobs):
        oversized = [j.name for j in jobs if j.slots > workers or j.memory > memory]
        raise ValueError(f"jobs exceed the available worker or memory budget: {', '.join(oversized)}")
    started = time.monotonic()
    pending = list(jobs)
    active = {}
    cancel = Event()
    status_counts = {}
    job_seconds = solver_seconds = 0.0
    with closing(connect(state)) as db, ThreadPoolExecutor(max_workers=min(workers, max(1, len(jobs)))) as pool:
        repeat_before = db.execute("SELECT COALESCE(MAX(number),0) FROM attempts").fetchone()[0]

        def publish(record):
            nonlocal job_seconds, solver_seconds
            status = record["status"]
            status_counts[status] = status_counts.get(status, 0) + 1
            job_seconds += record.get("seconds", 0)
            solver_seconds += record.get("solver_job_seconds", 0)
            report(record)

        def finish(future):
            job, (number, cap, folder, _) = active[future]
            try:
                result = future.result()
            except Exception as error:
                result = {"name": job.name, "key": job.key, "status": "error", "number": number,
                          "cap": cap, "folder": str(folder), "seconds": 0, "excerpt": str(error)[:1800]}
                write_json(folder / "result.json", result)
            with db:
                db.execute("UPDATE attempts SET status=?, finished=?, seconds=?, result_hash=? WHERE number=?",
                           (result["status"], time.time(), result["seconds"], file_hash(folder / "result.json"), number))
            active.pop(future)
            publish(result)

        def schedule():
            free_slots = workers - sum(j.slots for j, _ in active.values())
            free_memory = memory - sum(j.memory for j, _ in active.values())
            for job in pending[:]:
                if job.slots > free_slots or job.memory > free_memory:
                    continue
                ticket, skipped = reserve(db, state, job, repeat_reason, repeat_before, workers, memory)
                if not ticket and not skipped:
                    continue
                pending.remove(job)
                if skipped:
                    publish(skipped)
                    continue
                future = pool.submit(evaluate, job, ticket, cancel)
                active[future] = job, ticket
                free_slots -= job.slots
                free_memory -= job.memory
            if active:
                finished, _ = wait(active, timeout=1.0, return_when=FIRST_COMPLETED)
                for future in finished:
                    finish(future)
            elif pending:
                time.sleep(1)

        try:
            while pending or active:
                schedule()
        except KeyboardInterrupt:
            cancel.set()
            for future in list(active):
                finish(future)
    attempts = sum(n for k, n in status_counts.items() if k not in SKIPPED)
    return {"wall_seconds": round(time.monotonic() - started, 3), "summed_job_seconds": round(job_seconds, 3),
            "summed_solver_cube_seconds": round(solver_seconds, 3), "statuses": status_counts,
            "interrupted": cancel.is_set(), "not_started": len(pending),
            "duplicates_avoided": sum(status_counts.get(k, 0) for k in DUPLICATES),
            "timeout_rate": (status_counts.get("timeout", 0) + status_counts.get("open", 0)) / max(1, attempts)}
