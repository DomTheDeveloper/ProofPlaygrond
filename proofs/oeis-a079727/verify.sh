#!/usr/bin/env bash
set -euo pipefail
project_dir=$(cd -- "$(dirname -- "$0")" && pwd)
work_dir=$(mktemp -d)
trap 'rm -rf -- "$work_dir"' EXIT
cp "$project_dir"/{Block.lean,Complete.lean,lakefile.toml,lean-toolchain} "$work_dir/"
cd "$work_dir"
git init -q prior-source
git -C prior-source fetch --quiet --depth 1 \
  https://github.com/GuillaumeBAUD-coder/open-math-agents.git \
  f225addc007b9fb3e162bc5618bb84fa10f502e2
git -C prior-source show FETCH_HEAD:proofs/OeisA79727.conjecture4.lean > PriorProof.lean
test "$(git hash-object PriorProof.lean)" = c7bd50d3955dd9e4256e41315bb219c0e0bf8494
lake update
lake exe cache get
lake build Complete
lake env lean Complete.lean
