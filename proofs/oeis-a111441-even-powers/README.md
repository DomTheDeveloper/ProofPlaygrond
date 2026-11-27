# Prime-power divisibility indices are coprime to six

This independent Lean project proves the statement proposed in [open-math-agents PR #2808](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2808), for [OEIS A111441](https://oeis.org/A111441), and its positive-even-power generalization.

Let p₁ = 2, p₂ = 3, … be the primes in increasing order. For every pair of positive integers r and k,

    k divides Σ(i = 1,…,k) pᵢ^(2r)  ⇒  gcd(k, 6) = 1.

The square case r = 1 therefore excludes the residues 3 and 9 modulo 12 required by the proposed upstream statement. It also excludes every even index.

## Argument

Modulo 2, the first prime contributes zero and all later primes contribute one, so the sum is k − 1 for k ≥ 1. Modulo 3, the prime 3 contributes zero and every other prime raised to a positive even power contributes one, so the sum is k − 1 for k ≥ 2. If k divided the sum and either 2 or 3 divided k, that sum would simultaneously be 0 and −1 modulo that prime.

The positivity of r is necessary: exponent zero would give the sum k.

## Formal results

- `main`: exactly the proposition proposed in upstream PR #2808.
- `term_not_divisible_by_two` and `term_not_divisible_by_three`.
- `term_gcd_six`: the stronger square-case conclusion.
- `even_power_term_gcd_six`: the theorem for all positive even exponents.

The first two sequence definitions are preserved exactly from PR #2808. The generalized sum is separately defined as `sumEvenPowers`.

## Reproduction

This directory is an independent Lake project. It pins Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, leaving the repository's existing root project configuration untouched.

From this directory:

```bash
lake update
lake exe cache get Mathlib.NumberTheory.PrimeCounting Mathlib.Tactic.NormNum
lake env lean A111441.lean
```

The complete proof was replayed locally using that Lean version and pinned Mathlib. All four printed axiom reports returned only:

```text
[propext, Classical.choice, Quot.sound]
```

There are no admitted proofs, additional axioms, or native computation shortcuts. One unused-simp-argument warning does not affect the proof.

## Provenance and upstream status

The OEIS entry records Daniel Bamberger's broader even-power observation. The modular approach was inspired by the prime-square obstruction in [PR #2807](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2807); the proof and implementation here are independent.

The complete proof was also posted as a [contribution to statement PR #2808](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2808#issuecomment-7209808016). That statement must be reviewed and merged before the upstream checker can accept a proof submission targeting its generated module.

Agent: codex
Model: gpt-6.2-astra
