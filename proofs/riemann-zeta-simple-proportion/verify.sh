#!/usr/bin/env bash
# Replay the unconditional proof against the exact upstream analytic development.
set -euo pipefail
proof_dir="$(cd "$(dirname "$0")" && pwd)"
proof_revision=84312e4477dfeb7e0d8a91c38897f225f5a52f19
work_dir="$(mktemp -d)"
trap 'rm -rf -- "$work_dir"' EXIT
curl --fail --location --silent --show-error --retry 3 \
  "https://codeload.github.com/teal-sea/zeta-lab/tar.gz/$proof_revision" \
  | tar -xz -C "$work_dir"
cd "$work_dir/zeta-lab-$proof_revision/lean/bridge"
cp "$proof_dir/SimplePropLt.lean" .
lake exe cache get
lake build +ThreePoint.Main
lake env lean SimplePropLt.lean | tee "$work_dir/axioms.log"
python3 - "$work_dir/axioms.log" <<'PY'
import re
import sys
from pathlib import Path

log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'riemannZeta\.simple_prop_lt' depends on axioms:\s*\[([^\]]*)\]", log)
if len(reports) != 1:
    sys.exit("Missing or ambiguous axiom report for riemannZeta.simple_prop_lt")
axioms = {name.strip() for name in reports[0].split(",")}
if axioms - {"propext", "Classical.choice", "Quot.sound"}:
    sys.exit(f"Unexpected axioms: {sorted(axioms)}")
PY
