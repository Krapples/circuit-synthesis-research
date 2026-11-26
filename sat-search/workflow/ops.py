"""Administrative operations kept separate from experimental execution."""

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import HTTPRedirectHandler, Request, build_opener

from common import ROOT, atomic_text, digest, excerpt, file_hash, read_json, run_logged, write_json


REPOSITORY = "open-goat/pequalnp-proofs"
DESK = "https://pequalnp.com/desk"
STOP_NOTICE = f"https://raw.githubusercontent.com/{REPOSITORY}/main/STOP"
STEP = re.compile(r"[LDR]-(?:meta|gct)-[0-9]+(?:-[0-9]+)?\Z")
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
TEXT_EXTENSIONS = {".lean", ".py", ".ps1", ".json", ".jsonl", ".toml", ".md", ".txt", ".yml", ".yaml", ".sh", ".cpp", ".h"}
TEXT_FILENAMES = {".gitignore", ".gitattributes", "lean-toolchain", "Makefile"}


def stamp():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def operation_folder(state, kind):
    return state / "ops" / f"{time.time_ns()}-{kind}"


def command(state, kind, argv, cwd, timeout):
    folder = operation_folder(state, kind)
    result = run_logged(argv, cwd, folder, timeout)
    write_json(folder / "request.json", {"argv": argv, "cwd": str(cwd), "timeout": timeout})
    write_json(folder / "result.json", result)
    return result


def command_ok(result):
    return result["returncode"] == 0 and not result["timeout"] and not result["interrupted"]


def command_failure(result):
    return excerpt(result["stderr"]) or excerpt(result["stdout"]) or result["error"] or "command did not finish successfully"


def selected_paths(names):
    selected = []
    for name in names:
        source = ROOT / name
        path = source.resolve()
        if not path.is_relative_to(ROOT) or not path.is_file() or source.is_symlink():
            raise ValueError(f"expected an existing regular workspace file: {name}")
        selected.append(path)
    return list(dict.fromkeys(selected))


def normalize(paths):
    changed = []
    for path in paths:
        if path.suffix.lower() not in TEXT_EXTENSIONS and path.name not in TEXT_FILENAMES:
            raise ValueError(f"normalization requires a recognized text source: {path}")
        raw = path.read_bytes()
        encoding = "utf-16" if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig"
        text = raw.decode(encoding)
        if "\0" in text:
            raise ValueError(f"NUL in text file: {path}")
        cleaned = text.replace("\r\n", "\n").replace("\r", "\n")
        if cleaned.encode("utf-8") != raw:
            atomic_text(path, cleaned)
            changed.append(str(path.relative_to(ROOT)))
    return changed


def checkpoint(state, paths, message):
    names = [path.relative_to(ROOT).as_posix() for path in paths]
    if not names:
        raise ValueError("checkpoint requires explicit paths")
    stages = command(state, "git-index", ["git", "diff", "--cached", "--name-only", "-z"], ROOT, 20)
    if not command_ok(stages):
        raise ValueError(command_failure(stages))
    existing = set(Path(stages["stdout"]).read_text(encoding="utf-8").strip("\0").split("\0")) - {""}
    unrelated = existing - set(names)
    if unrelated:
        raise ValueError(f"checkpoint would include unrelated staged paths: {', '.join(sorted(unrelated))}")
    changed = normalize(paths)
    add = command(state, "git-stage", ["git", "-c", "core.autocrlf=false", "add", "--", *names], ROOT, 30)
    if not command_ok(add):
        raise ValueError(command_failure(add))
    check = command(state, "git-whitespace", ["git", "diff", "--cached", "--check"], ROOT, 30)
    if not command_ok(check):
        raise ValueError(command_failure(check))
    diff = command(state, "git-diff", ["git", "diff", "--cached", "--", *names], ROOT, 30)
    stat = command(state, "git-stat", ["git", "diff", "--cached", "--stat", "--", *names], ROOT, 30)
    if not command_ok(diff) or not command_ok(stat):
        raise ValueError(command_failure(diff if not command_ok(diff) else stat))
    result = {"normalized": changed, "diff_log": diff["stdout"], "staged_summary": excerpt(stat["stdout"])}
    if message and result["staged_summary"]:
        unchanged = command(state, "git-worktree", ["git", "-c", "core.autocrlf=false", "diff", "--quiet",
                                                    "--", *names], ROOT, 20)
        if not command_ok(unchanged):
            raise ValueError("selected worktree files changed after staging; inspect the diff and retry")
        commit = command(state, "git-commit", ["git", "-c", "core.autocrlf=false", "commit", "--only", "-m", message,
                                                "--", *names], ROOT, 90)
        if not command_ok(commit):
            raise ValueError(command_failure(commit))
        result.update(commit_summary=excerpt(commit["stdout"]), commit_log=commit["stdout"])
    return result


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def request(url, method="GET"):
    try:
        with build_opener(NoRedirect()).open(Request(url, method=method), timeout=12) as response:
            return response.status, response.read(65536)
    except HTTPError as error:
        return error.code, error.read(65536)
    except (URLError, OSError, TimeoutError):
        return None, b""


def read_lease(path):
    body = read_json(path)
    step, lease = body["gap"]["id"], body["lease"]["id"]
    if not isinstance(step, str) or not STEP.fullmatch(step) or not isinstance(lease, str) or not lease:
        raise ValueError("invalid desk lease file")
    return step, lease


def beat(lease):
    stop, _ = request(STOP_NOTICE)
    if stop == 200:
        return {"status": "upstream_stop"}
    status, raw = request(f"{DESK}/beat?{urlencode({'lease': lease})}", "POST")
    try:
        body = json.loads(raw)
    except (ValueError, UnicodeDecodeError):
        body = {}
    if not isinstance(body, dict):
        body = {}
    if status == 410 or body.get("withdrawn") is True:
        return {"status": "withdrawn" if body.get("withdrawn") is True else "expired", "http": status}
    if isinstance(body.get("lease"), dict):
        expires = body["lease"].get("expires_at")
        if not isinstance(expires, str) or not re.fullmatch(r"[0-9TtZz:.+\-]+", expires):
            expires = None
        return {"status": "renewed", "expires_at": expires, "http": status, "stop_check_http": stop}
    return {"status": "retry", "http": status, "stop_check_http": stop}


def heartbeat(state, path, seconds, once=False):
    if not 15 <= seconds <= 300:
        raise ValueError("heartbeat interval must be 15–300 seconds")
    step, lease = read_lease(path)
    stop = path.with_name(f"{step}.heartbeat-stop")
    folder = state / "desk"
    folder.mkdir(parents=True, exist_ok=True)
    lock = folder / f"{step}.watch.lock"
    try:
        fd = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        raise ValueError(f"a heartbeat watcher is already registered at {lock}") from None
    with os.fdopen(fd, "w", encoding="utf-8") as owner:
        owner.write(f"{socket.gethostname()} {os.getpid()}\n")
    try:
        wait = seconds
        while not stop.exists():
            event = {"at": stamp(), "step": step, **beat(lease)}
            with (folder / f"{step}.jsonl").open("a", encoding="utf-8", newline="\n") as log:
                log.write(json.dumps(event) + "\n")
            if once or event["status"] in {"withdrawn", "expired", "upstream_stop"}:
                return event
            wait = min(25, seconds) if event["status"] == "retry" else seconds
            until = time.monotonic() + wait
            while not stop.exists() and time.monotonic() < until:
                time.sleep(max(0, min(2, until - time.monotonic())))
        return {"at": stamp(), "step": step, "status": "local_stop"}
    finally:
        lock.unlink(missing_ok=True)


def pr_status(state, number, repository=REPOSITORY):
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) or number < 1:
        raise ValueError("invalid pull request")
    metadata = command(state, "pr", ["gh", "api", f"repos/{repository}/pulls/{number}", "--jq",
                        "{number,state,merged,mergeable_state,head:.head.sha,url:.html_url}"], ROOT, 20)
    if not command_ok(metadata):
        raise ValueError(command_failure(metadata))
    # Project comment bodies may mention lease credentials. Retain only controlled fields.
    expression = ('.[] | select(.user.type == "Bot") | . as $c | '
                  '($c.body | match("ACCEPTED|REJECTED|FAULT")?) as $m | '
                  '{status:$m.string,bot:$c.user.login,at:$c.created_at,url:$c.html_url}')
    comments = command(state, "pr-verdict", ["gh", "api", f"repos/{repository}/issues/{number}/comments", "--paginate",
                       "--jq", expression], ROOT, 20)
    if not command_ok(comments):
        raise ValueError(command_failure(comments))
    result = read_json(metadata["stdout"])
    result["bot_verdicts"] = [json.loads(line) for line in Path(comments["stdout"]).read_text(encoding="utf-8").splitlines() if line]
    result.update(at=stamp(), logs=[metadata["stdout"], comments["stdout"]])
    write_json(state / "desk" / f"{repository.replace('/', '_')}-{number}.json", result)
    return result


def lean_command(state, workspace, module, source, timeout, lake=None):
    workspace = workspace.resolve()
    lockfiles = [p for p in (workspace / "lean-toolchain", workspace / "lake-manifest.json") if p.is_file()]
    if len(lockfiles) != 2:
        raise ValueError("use the Lean workspace containing lean-toolchain and lake-manifest.json")
    executable = lake or shutil.which("lake") or str(Path.home() / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake"))
    if module and not MODULE.fullmatch(module):
        raise ValueError("module must be a Lean module name")
    metadata = command(state, "lean-version", [executable, "env", "lean", "--version"], workspace, 20)
    if not command_ok(metadata):
        raise ValueError(command_failure(metadata))
    profile = {"workspace": str(workspace), "toolchain": excerpt(metadata["stdout"]),
               "lockfiles": {p.name: file_hash(p) for p in lockfiles}}
    profile_path = state / "lean" / (digest(profile) + ".json")
    write_json(profile_path, profile)
    argv = [executable, "build", module] if module else [executable, "env", "lean", str(source.resolve())]
    result = command(state, "lean-build" if module else "lean-check", argv, workspace, timeout)
    return {"status": "ok" if command_ok(result) else "open" if result["timeout"] else "error",
            "cached_environment": str(profile_path), "log": result["stdout"], "stderr": result["stderr"],
            "seconds": result["seconds"], "excerpt": None if command_ok(result) else command_failure(result)}
