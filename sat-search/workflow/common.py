"""Shared paths, JSON handling and bounded process capture for research tools."""

import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[2]
SAT = ROOT / "sat-search"


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def atomic_text(path, body):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(body)
            handle.flush()
            os.fsync(handle.fileno())
        if path.is_file():
            os.chmod(temp, path.stat().st_mode)
        os.replace(temp, path)
    finally:
        if os.path.exists(temp):
            os.unlink(temp)


def write_json(path, body):
    atomic_text(path, json.dumps(body, ensure_ascii=False, indent=2, sort_keys=True, allow_nan=False) + "\n")


def digest(body):
    return hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()).hexdigest()


def file_hash(path):
    with Path(path).open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def excerpt(path, limit=1800):
    with Path(path).open("rb") as handle:
        handle.seek(max(0, handle.seek(0, os.SEEK_END) - limit))
        return handle.read(limit).decode("utf-8", errors="replace").strip()


def process_alive(pid):
    if type(pid) is not int or pid <= 0:
        raise ValueError("invalid process ID")
    if os.name != "nt":
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        except PermissionError:
            return True
        return True
    import ctypes
    from ctypes import wintypes

    api = ctypes.WinDLL("kernel32", use_last_error=True)
    api.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    api.OpenProcess.restype = wintypes.HANDLE
    api.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    api.WaitForSingleObject.restype = wintypes.DWORD
    api.CloseHandle.argtypes = [wintypes.HANDLE]
    handle = api.OpenProcess(0x100000, False, pid)
    if not handle:
        return ctypes.get_last_error() != 87  # ERROR_INVALID_PARAMETER for a missing PID
    try:
        return api.WaitForSingleObject(handle, 0) != 0  # WAIT_OBJECT_0 on a terminated process
    finally:
        api.CloseHandle(handle)


def kill_tree(process, cleanup_log):
    if os.name == "nt":
        try:
            with cleanup_log.open("ab") as log:
                subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                               stdout=log, stderr=log, timeout=8, check=False)
        except (OSError, subprocess.TimeoutExpired):
            pass
        if process.poll() is None:
            process.kill()
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def run_logged(argv, cwd, folder, timeout, *, env=None, stop=None, grace=7, cancel=None):
    """Capture complete child streams. The optional stop file requests a graceful timeout."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    stdout, stderr = folder / "stdout.log", folder / "stderr.log"
    cleanup_log = folder / "cleanup.log"
    started = time.monotonic()
    timeout_hit = False
    interrupted = False
    error = None
    returncode = None
    with stdout.open("wb") as out, stderr.open("wb") as err:
        try:
            process = subprocess.Popen(argv, cwd=cwd, stdout=out, stderr=err, stdin=subprocess.DEVNULL,
                                       env=env, start_new_session=os.name != "nt")
        except OSError as exc:
            error = str(exc)
            err.write((error + "\n").encode())
        else:
            try:
                write_json(folder / "process.json", {"pid": process.pid})
                deadline = started + timeout
                while True:
                    if cancel is not None and cancel.is_set():
                        raise KeyboardInterrupt
                    remaining = max(0, deadline - time.monotonic())
                    try:
                        process.wait(timeout=min(1, remaining) if cancel is not None else remaining)
                        break
                    except subprocess.TimeoutExpired:
                        if time.monotonic() >= deadline:
                            raise
            except (subprocess.TimeoutExpired, KeyboardInterrupt) as exc:
                timeout_hit = isinstance(exc, subprocess.TimeoutExpired)
                interrupted = not timeout_hit
                if stop is not None:
                    Path(stop).touch()
                    try:
                        process.wait(timeout=grace)
                    except (subprocess.TimeoutExpired, KeyboardInterrupt):
                        pass
                if process.poll() is None:
                    kill_tree(process, cleanup_log)
                process.wait()
            except OSError:
                kill_tree(process, cleanup_log)
                process.wait()
                raise
            returncode = process.returncode
    return {"seconds": round(time.monotonic() - started, 6), "returncode": returncode,
            "timeout": timeout_hit, "interrupted": interrupted, "error": error,
            "stdout": str(stdout), "stderr": str(stderr),
            "cleanup": str(cleanup_log) if cleanup_log.exists() else None}
