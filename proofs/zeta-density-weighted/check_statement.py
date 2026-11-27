"""Compare the proof's definitions and theorem signature to a Formal Conjectures checkout."""
from pathlib import Path
import re
import subprocess
import sys

PIN = "f606af160664c5a10952e9a957b100a1cd45bbeb"
API = "FormalConjecturesForMathlib/NumberTheory/RiemannZetaZeros.lean"
TARGET = "FormalConjectures/Wikipedia/DensityHypothesis.lean"
ROOT = Path(__file__).resolve().parent


def upstream(repo, path):
    return subprocess.check_output(["git", "-C", repo, "show", f"{PIN}:{path}"])


def count_definition(text):
    start = text.index("noncomputable abbrev zetaZeroCount ")
    return text[start:].split("\n\n", 1)[0].strip()


def theorem_signature(text):
    start = text.index("theorem density_hypothesis_zeta_zeros ")
    return re.sub(r"\s+", " ", text[start:].split(":=", 1)[0]).strip()


def check(label, actual, expected):
    if actual != expected:
        raise SystemExit(f"Mismatch in {label}")
    print(f"PASS {label}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 check_statement.py PATH_TO_FORMAL_CONJECTURES")
    repo = sys.argv[1]
    official = upstream(repo, TARGET).decode()
    check("Complex.zeroCountOn and its source module",
          (ROOT / "DensityHypothesis/ZeroCount.lean").read_bytes(), upstream(repo, API))
    check("DensityHypothesis.zetaZeroCount",
          count_definition((ROOT / "DensityHypothesis/Count.lean").read_text()), count_definition(official))
    check("density_hypothesis_zeta_zeros signature",
          theorem_signature((ROOT / "DensityHypothesis.lean").read_text()), theorem_signature(official))
