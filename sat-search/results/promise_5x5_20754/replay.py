"""Replay the packed certificate and exact-model proof in the project Lean workspace."""

from argparse import ArgumentParser
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[3]
PACKET = Path(__file__).resolve().parent


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--lake", help="Path to the pinned Lake executable")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()

    core = (PACKET / "ActiveBudget.lean").read_text(encoding="utf-8")
    model = (PACKET / "ExactModel.lean").read_text(encoding="utf-8")
    project_import, core_import, body = model.split("\n", 2)
    mathlib_import, packed = core.split("\n", 1)
    if not project_import.startswith("import PEqualNP.") or core_import != "import ActiveBudget":
        raise ValueError("unexpected proof-packet imports")
    source = f"{mathlib_import}\n{project_import}\n{packed}\n{body}"
    source += "\n#print axioms ActiveBudget20754.project_to_packed\n"
    source += "\n#print axioms ActiveBudget20754.not_rep_size_at_most_seven\n"
    source += "#print axioms ActiveBudget20754.rep_size_at_most_eight\n"

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
        return subprocess.run(command, cwd=ROOT, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
