import Init

/-!
Finite kernel checks for the prime-level congruences on OEIS A364114,
A364118 and A364119. The universal proof is in README.md.
-/

namespace BalaPrimeDefect

def binom (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => binom n k * (n - k) / (k + 1)

/-- Pack the coefficients in a carry-free radix and extract T_r(n). -/
def rowMod (r n modulus : Nat) : Nat :=
  let width := n * (3 * r + 1) + 1
  let radix := 2 ^ width
  let legendre := (List.range (n + 1)).foldr
    (fun j value => binom n j * binom (n + j) j + radix * value) 0
  let packed := (1 + radix) ^ n * legendre ^ r
  ((packed >>> (width * n)) % radix) % modulus

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem row_values_at_seven :
    rowMod 3 7 (7^5) = 3094 ∧ rowMod 3 6 (7^5) = 16122 ∧
    rowMod 4 7 (7^5) = 7898 ∧ rowMod 4 6 (7^5) = 7204 := by decide

theorem row_values_at_eleven :
    rowMod 3 11 (11^5) = 102494 ∧ rowMod 3 10 (11^5) = 57234 ∧
    rowMod 4 11 (11^5) = 74545 ∧ rowMod 4 10 (11^5) = 106481 := by decide

theorem linear_congruences_at_seven :
    (3 * rowMod 3 7 (7^5)) % (7^5) =
      (10 + 11 * rowMod 3 6 (7^5)) % (7^5) ∧
    (7 * rowMod 4 7 (7^5)) % (7^5) =
      (46 + 17 * rowMod 4 6 (7^5)) % (7^5) := by decide

theorem multiplicative_congruences_at_seven :
    ((rowMod 3 7 (7^5))^21) % (7^5) =
      (7^21 * (rowMod 3 6 (7^5))^11) % (7^5) ∧
    ((rowMod 4 7 (7^5))^63) % (7^5) =
      (9^63 * (rowMod 4 6 (7^5))^17) % (7^5) := by decide

#print axioms row_values_at_seven
#print axioms row_values_at_eleven
#print axioms linear_congruences_at_seven
#print axioms multiplicative_congruences_at_seven

end BalaPrimeDefect
