#!/usr/bin/env bash
set -euo pipefail

g++ -std=c++17 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic \
  chomp_export_p_ranks.cpp -o chomp_export_p_ranks
g++ -std=c++17 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic \
  chomp_proof_dag.cpp -o chomp_proof_dag

./chomp_export_p_ranks 4 10 p4x10.bin 2> p4x10-export.log
./chomp_proof_dag p4x10.bin 100000 10,8,8,7 | tee p4x10-dag.log
grep -F 'P=75 prefixes=285 last_rank=967' p4x10-export.log
grep -F 'COMPLETE nodes=470 P=58 N=412 edges=1306 maxFan=32' p4x10-dag.log

/usr/bin/time -v ./chomp_export_p_ranks 10 42 p10x42.bin \
  > p10x42-export.out 2> p10x42-export.log
test "$(stat -c%s p10x42.bin)" -gt 800000000
grep -E '^P=[0-9]+ prefixes=3042312350 last_rank=' p10x42-export.log

set +e
/usr/bin/time -v ./chomp_proof_dag p10x42.bin 2000000 \
  42,42,42,42,35,35,35,35,35,35 \
  42,42,42,42,42,42,29,29,29,29 \
  42,42,42,42,42,42,42,25,25,25 \
  > p10x42-dag.out 2> p10x42-dag.log
status=$?
set -e
if [[ $status -ne 0 && $status -ne 3 ]]; then
  cat p10x42-dag.log >&2
  exit "$status"
fi
grep -E '^(COMPLETE|LIMIT) nodes=' p10x42-dag.out

{
  echo '# Chomp 10x42 kernel-certificate feasibility'
  echo
  echo '## Full P database'
  tail -n 20 p10x42-export.log
  echo
  echo '## Shared proof DAG'
  cat p10x42-dag.out
  tail -n 30 p10x42-dag.log
} | tee certificate-feasibility.md
