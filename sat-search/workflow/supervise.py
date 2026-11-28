"""Wall-bounded, independently observable CPU jobs with owned-process cleanup."""
from dataclasses import dataclass
import json
import math
import multiprocessing
from multiprocessing.connection import wait
import time
import traceback


@dataclass(frozen=True)
class Job:
    """A unique job key, picklable worker arguments, and JSON case-start details."""

    key: str | int
    arguments: tuple
    details: dict


def _worker_entry(sender, worker, arguments):
    def report(event, *, phase=None, throttle=False, **data):
        if event in {"result", "worker_error"} or "case" in data:
            raise ValueError("result, worker_error and case are reserved supervisor fields")
        sender.send((event, phase, throttle, data))

    try:
        result = worker(report, *arguments)
        if not isinstance(result, dict) or {"event", "case"} & result.keys():
            raise ValueError("worker results must be dicts without event or case keys")
        sender.send(("result", None, False, result))
    except Exception:
        sender.send(("worker_error", None, False, {"traceback": traceback.format_exc()}))
        raise SystemExit(1)
    finally:
        sender.close()


def emit(event, **data):
    print(json.dumps({"event": event, **data}, separators=(",", ":")), flush=True)


def _stop_worker(process):
    if process.is_alive():
        process.terminate()
    process.join(timeout=2)
    if process.is_alive():
        process.kill()
        process.join()


def run_jobs(jobs, worker, *, workers, wall, heartbeat, emit=emit):
    """Run jobs in isolated processes and stream progress from the parent.

    The worker is a module-level function accepting report as its first argument.
    It returns a dict for the terminal result or raises to signal an error.
    Reserve event and case for supervisor routing, and pid in job details.
    Workers run in-process code. Commands with subprocess trees use run_logged.
    Callers must guard their entry point with if __name__ == "__main__".
    """
    if not isinstance(workers, int) or not 1 <= workers <= 22:
        raise ValueError("workers must be an integer between 1 and 22")
    if not all(math.isfinite(limit) and limit > 0 for limit in (wall, heartbeat)):
        raise ValueError("wall and heartbeat limits must be finite and positive")
    context = multiprocessing.get_context("spawn")
    pending = iter(jobs)
    active = {}
    count_errors = 0
    count_results = 0
    count_wall = 0
    try:
        while True:
            while len(active) < workers:
                item = next(pending, None)
                if item is None:
                    break
                if {"case", "event", "pid"} & item.details.keys():
                    raise ValueError("job details cannot include case, event or pid")
                case = item.key
                receiver, sender = context.Pipe(duplex=False)
                process = context.Process(target=_worker_entry, args=(sender, worker, item.arguments))
                now = time.monotonic()
                try:
                    process.start()
                except BaseException:
                    receiver.close()
                    raise
                finally:
                    sender.close()
                active[receiver] = {
                    "process": process, "case": case, "start": now,
                    "deadline": now + wall,
                    "next_heartbeat": now + heartbeat, "phase": {"event": "starting"},
                    "last_report": None,
                    "terminal": False,
                }
                emit("case_start", case=case, pid=process.pid, **item.details)
            if not active:
                break
            now = time.monotonic()
            next_event = min(
                state["deadline"] if state["terminal"] else
                min(state["deadline"], state["next_heartbeat"])
                for state in active.values()
            )
            ready = wait(list(active), timeout=max(0, min(0.1, next_event - now)))
            for receiver in ready:
                state = active[receiver]
                # Drain queued messages before classifying a process exit or timeout.
                for _ in range(32):
                    try:
                        if not receiver.poll():
                            break
                        message = receiver.recv()
                    except (EOFError, BrokenPipeError):
                        process = state["process"]
                        process.join(timeout=0.1)
                        if process.is_alive():
                            break
                        if not state["terminal"] or process.exitcode != 0:
                            count_errors += 1
                            emit("case_error", case=state["case"], exitcode=process.exitcode)
                        receiver.close()
                        process.close()
                        del active[receiver]
                        break
                    event, phase, throttle, message = message
                    if phase is not None:
                        state["phase"] = {"event": event, **phase}
                    if event in {"result", "worker_error"}:
                        state["terminal"] = True
                        state["deadline"] = time.monotonic() + 2
                    if not throttle:
                        state["last_report"] = None
                    else:
                        now = time.monotonic()
                        last_report = state["last_report"]
                        if last_report is not None and now - last_report < heartbeat:
                            continue
                        state["last_report"] = now
                    if event == "result":
                        count_results += 1
                    emit(event, case=state["case"], **message)
            now = time.monotonic()
            for receiver, state in list(active.items()):
                elapsed = now - state["start"]
                if now >= state["deadline"]:
                    _stop_worker(state["process"])
                    if state["terminal"]:
                        count_errors += 1
                        emit("worker_cleanup_limit", case=state["case"])
                    else:
                        count_wall += 1
                        emit("wall_limit", case=state["case"], elapsed_seconds=round(elapsed, 3),
                             last_worker_event=state["phase"])
                    receiver.close()
                    state["process"].close()
                    del active[receiver]
                elif not state["terminal"] and now >= state["next_heartbeat"]:
                    emit("heartbeat", case=state["case"], pid=state["process"].pid,
                         elapsed_seconds=round(elapsed, 3), last_worker_event=state["phase"])
                    state["next_heartbeat"] = now + heartbeat
    finally:
        for receiver, state in active.items():
            _stop_worker(state["process"])
            receiver.close()
            state["process"].close()
    emit("run_end", results=count_results, wall_limits=count_wall, worker_errors=count_errors)
    return int(count_errors != 0)
