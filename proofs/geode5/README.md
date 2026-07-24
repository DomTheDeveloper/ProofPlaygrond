# Geode5 formal proof

This directory turns the computational certificate from `geode5_bounty_solution.zip` into Lean proof layers for

```text
G(1000,1000,1000,1000,1000).
```

## Completed Lean layer

`Geode5CRT.lean` formalizes:

- parsing the exact 8,367-digit answer and all 480 residue pairs;
- the fact that the 480 moduli are pairwise coprime;
- canonicality of every residue;
- agreement of the proposed answer with every stored residue;
- the hyper-Catalan upper bound;
- the strict inequality `upperBound < product moduli`;
- Chinese-remainder combination of all residue congruences;
- uniqueness of any candidate below the upper bound;
- the final conditional theorem `geode5_1000_of_certificate`.

## Remaining formal bridge

The ZIP contains a correct computational proof architecture, but not Lean source for the five-state recurrence. The remaining modules must prove:

1. the alternating-sum definition of `geode5Diagonal` equals the one-variable moment coefficient formula;
2. the symbolic Euclidean divisions yield the five-state lower-triangular recurrence;
3. the modular recurrence computes each of the 480 stored residues;
4. `geode5Diagonal 1000` is nonnegative and below the hyper-Catalan bound.

Once these are supplied, `geode5_1000_of_certificate` closes the exact benchmark equality with no `sorry` or custom axiom.

## Audit

The workflow `.github/workflows/geode5-formal-proof-audit.yml` overlays this proof module onto immutable Formal Conjectures commit
`6db9713c4c2036afdad119eda930b4d1a8da3250` and compiles it with Lean 4.27 and warnings as errors.
