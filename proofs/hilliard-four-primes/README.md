# Four primes between consecutive positive cubes

For each positive integer $n$, at least four distinct primes lie strictly between $n^3$ and $(n+1)^3$. The bound is sharp because the first interval contains exactly 2, 3, 5 and 7. Cino Hilliard recorded the conjecture in 2003. [OEIS A060199](https://oeis.org/A060199)

## Lean proof

`Hilliard.lean` states `CubePrimes.hilliard_four_primes_between_cubes` for all positive natural numbers. It counts a finite set of primes using `Finset.Ioo`, which excludes both endpoints. The theorem takes only the integer and its positivity proof.

`BoundSolution.lean` uses the compact RH proof and the equivalence of RH with Schoenfeld’s explicit bound for Chebyshev’s ψ. It is the same source file that Andrew Sutherland checked in his end-to-end Schoenfeld project. [MIT verification](https://math.mit.edu/~drew/shortgrh/#schoenfeld)

`CubeProof.lean` proves `CubePrimes.four_primes_of_schoenfeld` and `CubePrimes.four_primes_at_one`. For indices 1 through 255 it verifies four ordered prime witnesses in each interval using kernel arithmetic. For larger indices it proves that the increase in Chebyshev’s θ across the interval exceeds three times the log of the upper endpoint. At most three primes could contribute only that amount.

Chamberland and Straub’s theorem on primes between consecutive real powers also yields the four-prime conclusion under RH, together with a finite check. This project formalizes a direct argument from Schoenfeld’s estimate. [Chamberland and Straub](https://arxiv.org/abs/2602.22502)

## Build

On Linux with Git, Python 3 and elan installed, run these commands from this directory.

```sh
bash setup.sh
bash check-cached.sh
```

The second command checks that the published RH modules correspond to the pinned RH source tree and toolchain. The upstream cache verifier checks the downloaded hashes. Lean then compiles Schoenfeld’s library, the cube-prime proof and the theorem that connects them. The final line prints the theorem’s axioms.

To rebuild the compact RH proof from source after `bash setup.sh`, run the following commands in the same directory.

```sh
ulimit -s unlimited
lake build
lake env lean Hilliard.lean
```

The workflow builds the integrated theorem and checks its axiom report against `propext`, `Classical.choice` and `Quot.sound`. The project pins Lean 4.35.0 and Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`. [Compact RH source](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact) · [Schoenfeld source](https://github.com/AndrewVSutherland/schoenfeld-rh-lean/tree/0e52d7b1a83fb548f6395546828a923a2e3d9627)
