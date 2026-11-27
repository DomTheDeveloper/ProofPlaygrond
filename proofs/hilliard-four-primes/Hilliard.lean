import CubeProof
import BoundSolution

/-! Hilliard's conjecture on prime counts in consecutive cube intervals (OEIS A060199). -/
namespace CubePrimes

/-- Every open interval between consecutive positive integer cubes contains at least four primes. -/
theorem hilliard_four_primes_between_cubes (n : ℕ) (hn : 1 ≤ n) :
    4 ≤ ((Finset.Ioo (n^3) ((n+1)^3)).filter Nat.Prime).card :=
  four_primes_of_schoenfeld schoenfeld_strict_bound n hn

#print axioms hilliard_four_primes_between_cubes
end CubePrimes
