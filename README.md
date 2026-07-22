# Proof Playground

This repository is the working sandbox for Lean proof development, verification, experiments, and temporary test files.

## Promotion pipeline

1. Develop and verify in `DomTheDeveloper/ProofPlaygrond`.
2. After the theorem statement and proof are stable and checks pass, port the proof to `DomTheDeveloper/formal-conjectures`.
3. After downstream checks pass, open a focused pull request to the official Google DeepMind Formal Conjectures repository.

`DomTheDeveloper/crl` is legacy and must not receive new proof work.
