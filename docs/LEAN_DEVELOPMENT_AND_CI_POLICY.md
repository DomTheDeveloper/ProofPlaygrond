# Lean development and CI policy

This repository is the development and verification sandbox for Dominic Dabish's Lean work.

## Core rule

**Do not use GitHub Actions as the edit–compile–debug loop.**

Use this order:

1. AXLE MCP, CLI, Python client, or HTTP API for iterative elaboration and proof repair.
2. Exact local pinned Lean for targeted compilation when available.
3. `ProofPlaygrond`'s **Manual Lean audit** workflow for one observable, immutable kernel audit.
4. `DomTheDeveloper/formal-conjectures` only after the proof is stable.
5. Google DeepMind Formal Conjectures only after the fork's final gate passes.

## Development phase

- Work on a branch; a pull request is not a workflow button.
- Check only the changed theorem/file with AXLE.
- Run `lake env lean path/to/Audit.lean` or `lake --wfail build Module.Name`, not a repository-wide build.
- Keep an audit file containing the terminal theorem and `#print axioms` commands.
- Reject `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `Lean.trustCompiler`, `Lean.ofReduce`, and `Lean.ofReduceBool` in the proof chain.
- Push freely, but do not create multiple audit PRs or operating-system variants.

## Kernel-audit phase

Use `.github/workflows/manual-lean-audit.yml` through `workflow_dispatch`.

Required inputs:

- source repository;
- preferably an immutable commit SHA;
- one Lean file or Lake module target;
- optional axiom-audit file;
- explicit files/directories for the placeholder scan.

Default to one Linux runner. macOS or ARM is justified only by a concrete platform/toolchain failure. Repeating the same safe Lean proof on several operating systems is operational redundancy, not additional mathematical proof strength.

The workflow has a repository-wide bounded concurrency group: one audit runs and at most one newer audit waits. Do not create theorem-specific workflow files for routine verification.

## Promotion phase

A proof moves to `DomTheDeveloper/formal-conjectures` only when:

- the exact theorem statement is preserved;
- targeted Lean compilation passes;
- the terminal axiom audit contains no forbidden dependency;
- the proof source is pinned to a commit SHA;
- the PR is ready for review rather than being used as a development trigger.

The fork should perform a full repository build once at the promotion/merge gate, not on every draft proof commit.

## Emergency cancellation

Do not rely on a GitHub Actions workflow to cancel a congested Actions queue: that workflow also needs a runner and can become trapped behind the jobs it is meant to cancel.

Use the GitHub REST API or `gh run cancel --force` from outside Actions. The helper script is `scripts/cancel-actions.sh`.

## Workflow hygiene

- One generic manual audit workflow, not one workflow per theorem.
- One proof branch per theorem.
- At most one promotion PR per theorem.
- Draft PRs should receive only lightweight metadata/lint checks.
- Full Lean and documentation builds belong on ready-for-review, explicit manual dispatch, merge-group, or main-branch events.
- Every expensive workflow must use concurrency controls.
- Never hedge routine audits across Linux, ARM, macOS, and Windows simultaneously.
- Remove temporary workflow files after their evidence is recorded.
