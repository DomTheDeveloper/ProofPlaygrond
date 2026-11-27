import Init

/-!
Finite evaluations of the Legendre array in OEIS A364113, A364116 and A364117.
The binomial expansion used here is proved in Section 1 of the accompanying note.
Evaluation uses Lean's kernel. The general congruence proofs are in README.md.
-/

namespace BalaLegendre

def binom (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => binom n k * (n - k) / (k + 1)

/-- The degree-n coefficient of (1+y)^n P_n(1+2y)^r is T(r,n).
    Every coefficient is at most the sum of the coefficients. This sum is
    2^n P_n(3)^r ≤ 2^(n*(3*r+1)), since binom(n+j,j) ≤ 2^(2*n).
    With the radix below, evaluation packs the coefficients without carries. -/
def rowMod (r n modulus : Nat) : Nat :=
  let width := n * (3 * r + 1) + 1
  let radix := 2 ^ width
  let legendre := (List.range (n + 1)).foldr
    (fun j value => binom n j * binom (n + j) j + radix * value) 0
  let packed := (1 + radix) ^ n * legendre ^ r
  ((packed >>> (width * n)) % radix) % modulus

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem a364116_counterexample :
    rowMod 3 3 10000 = 5623 ∧ rowMod 3 3 81 = 34 ∧ (2 * 3 + 1 : Nat) % 81 = 7 ∧
      rowMod 3 3 81 ≠ (2 * 3 + 1 : Nat) % 81 := by decide

theorem a364117_prime_examples :
    rowMod 6 5 125 = 13 ∧ rowMod 8 7 343 = 17 := by decide

theorem a364117_shifted_examples :
    rowMod 3 2 81 = 1 ∧ rowMod 9 8 243 = 1 ∧ rowMod 5 4 625 = 1 := by decide

theorem a364116_diagonal_examples :
    rowMod 5 5 625 = 11 ∧ rowMod 4 4 125 = 1 := by decide

theorem shifted_three_unit_examples :
    rowMod 1 8 27 = 19 ∧ rowMod 2 8 27 = 19 := by decide

theorem a364113_cubic_towers_row_three :
    rowMod 3 25 15625 = rowMod 3 5 15625 ∧
    rowMod 3 24 15625 = rowMod 3 4 15625 := by decide

#print axioms a364116_counterexample
#print axioms a364117_prime_examples
#print axioms a364117_shifted_examples
#print axioms a364116_diagonal_examples
#print axioms shifted_three_unit_examples
#print axioms a364113_cubic_towers_row_three

end BalaLegendre
