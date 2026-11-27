"""Replay the packed certificate and exact-model proof in the project Lean workspace."""

from argparse import ArgumentParser
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[3]
PACKET = Path(__file__).resolve().parent
KERNEL_MODULES = ("PackedModel", "ExactModel", "ReadOnce", "TraceDemand", "KernelExact")
DIAGNOSTIC_MODULES = ("PackedModel", "ExactModel", "ActiveBudget", "DiagnosticLower")
KERNEL_THEOREMS = (
    "ActiveBudget20754.project_to_packed",
    "ActiveBudget20754.rep_size_at_most_eight",
    "Promise20754.no_read_once",
    "Promise20754.no_once_shared",
    "Promise20754.no_seven_rule_trace",
    "ActiveBudget20754.kernel_not_rep_size_at_most_seven",
)
DIAGNOSTIC_THEOREMS = (
    "ActiveBudget20754.project_to_packed",
    "ActiveBudget20754.not_rep_size_at_most_seven",
    "ActiveBudget20754.rep_size_at_most_eight",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def proof_source(modules, theorems):
    imports = {}
    bodies = []
    for module in modules:
        source = (PACKET / f"{module}.lean").read_text(encoding="utf-8")
        body = []
        for line in source.splitlines():
            if line.startswith("import "):
                imported = line.removeprefix("import ")
                if imported not in modules:
                    imports[imported] = None
            else:
                body.append(line)
        bodies.append("\n".join(body))
    axioms = "\n".join(f"#print axioms {theorem}" for theorem in theorems)
    return "\n".join([*(f"import {module}" for module in imports), *bodies, "", axioms, ""])


def read_axioms(output, theorems):
    audit = {}
    for theorem in theorems:
        found = re.search(r"'" + re.escape(theorem) + r"' depends on axioms: \[([^\]]*)\]", output)
        if found:
            audit[theorem] = [part.strip() for part in found[1].split(",")]
        elif f"'{theorem}' does not depend on any axioms" in output:
            audit[theorem] = []
        else:
            raise ValueError(f"missing axiom report for {theorem}")
    return audit


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("kernel", "diagnostic"), default="kernel")
    parser.add_argument("--lake", help="Path to the pinned Lake executable")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()

    kernel = args.mode == "kernel"
    modules = KERNEL_MODULES if kernel else DIAGNOSTIC_MODULES
    theorems = KERNEL_THEOREMS if kernel else DIAGNOSTIC_THEOREMS
    source = proof_source(modules, theorems)

    build_root = ROOT / ".research"
    build_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="promise-20754-", dir=build_root) as directory:
        path = Path(directory) / "Replay.lean"
        path.write_text(source, encoding="utf-8", newline="\n")
        command = [
            sys.executable, "-B", "sat-search/workflow/research.py",
            "lean", "pequalnp-proofs/lean", "--source", str(path),
            "--timeout", str(args.timeout),
        ]
        if args.lake:
            command += ["--lake", args.lake]
        checked = subprocess.run(command, cwd=ROOT, check=False, capture_output=True, text=True, encoding="utf-8")
        if checked.stderr:
            sys.stderr.write(checked.stderr)
        summary = json.loads(checked.stdout)
        summary["mode"] = args.mode
        if checked.returncode == 0:
            summary["axioms"] = read_axioms(Path(summary["log"]).read_text(encoding="utf-8"), theorems)
            if kernel and any(set(used) - STANDARD_AXIOMS for used in summary["axioms"].values()):
                summary["status"] = "unexpected_axiom"
        print(json.dumps(summary))
        return checked.returncode or int(summary["status"] != "ok")


if __name__ == "__main__":
    raise SystemExit(main())
