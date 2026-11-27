# Partial solutions for OEIS A245211 and A245212

Dominic Aziz Dabish (DomTheDeveloper). The two original conjectures were posed by Jaroslav Krizek in 2014.

## A245211

**Current bound.** Every fixed point other than 21 has least prime at least 257. Two exact programs have covered 149,849 exponent patterns through least prime 251. See the [extension, proof and replay instructions](A245211/extension/README.md).

If a positive integer has a prime divisor at most 199, it is a fixed point of A245211 exactly when it equals 21. The bound is on the least prime factor. There is no cutoff on the size of the integer. The result is computer-assisted. Two exhaustive programs agree on the fixed points and on all 89,439 ordered exponent patterns, separately for each prime. Both the finiteness proof and the pruning arguments are in the [proof note, page 5](A245212/A245212-Density-Zero.pdf).

From this directory run the following commands with Python 3. The final column gives all the fixed points for a specified least prime. The integer search also counts search nodes.

```sh
python3 A245211/search_fixed_points.py 199
python3 A245211/check_fixed_points.py 199
```

The corresponding output files are [integer-certified.txt](A245211/integer-certified.txt) and [rational-certified.txt](A245211/rational-certified.txt). The prime-by-prime counts are in [range-verified.json](A245211/range-verified.json). The next prime is 211. The proof note also derives a density bound for A245211 from uniqueness at fixed cofactor.

## A245212

A uniform lower bound on φ(n)(a(n) − σ(n)) proves the entire odd-input branch n ≤ 2φ(n) for numbers with at least two different prime factors. See the [theorem, short proof, Lean source and independent check](A245212/totient-gap.md).

Let E(X) count the integers between 1 and X with a(n) = σ(n). Its natural density is zero. For every pair of cutoffs X and y with y positive, E(X) ≤ Ψ(X,y) + ⌊X/y⌋, where Ψ counts positive y-smooth integers. [Kernel-checked Lean source](https://github.com/DomTheDeveloper/open-math-agents/blob/077fa5a8106ea2fe4cbb16236ca655e9edb353b7/reductions/OeisA245212.conjecture.R1.H2.R1.lean) · [Left to Solve submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1376).

The [quantitative note](A245212/A245212-Density-Zero.pdf) derives E(X)/X < 1/120,000,000 for every X ≥ 10¹⁰⁰, a stretched-exponential bound and convergence of the reciprocal sum. The explicit estimate has two exact computational certificates.

```sh
python3 A245212/exact_bound.py
python3 A245212/block_bound.py
python3 A245212/direct_checks.py
```

The [odd-input proof](A245212/odd-three-primes/A245212-Odd-Three-Prime-Certificate.pdf) and its two exact programs show that any odd counterexample has at least four distinct primes and satisfies n > 2φ(n). It includes the optimal two-prime estimate 8(a(n) − σ(n)) ≥ nτ(n). The [accepted two-prime reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1048) contains the Lean formalization of the inequality.

```sh
python3 A245212/odd-three-primes/exact_three_primes.py
python3 A245212/odd-three-primes/crosscheck_three_primes.py
```

The [odd-part note](A245212/A245212-Prime-Powers-and-Density.pdf) excludes every positive integer with exactly one distinct odd prime factor, reduces each fixed odd part greater than one to at most one possible exponent of two, and proves that the set of parity mismatches has natural density π²/12.

## Sources

- Jaroslav Krizek, the original sequences and conjectures. [OEIS A245211](https://oeis.org/A245211) · [OEIS A245212](https://oeis.org/A245212).
- Earlier A245211 product analysis and fixed-point restrictions. [Product and monotonicity](https://github.com/umaia1234/agentic-conjectures/blob/main/problems/oeis-a245211/DETAILS.md) · [Mar Allen Sugui's preprint](https://zenodo.org/records/24437886) · [Sugui's formal-conjectures submission](https://github.com/google-deepmind/formal-conjectures/pull/8119).
- BetAdmin237's odd/even reduction for A245212. [Left to Solve #488](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/488).

The two complete Krizek conjectures remain open. The certificates document the exact partial statements above. Research priority has not been established.
