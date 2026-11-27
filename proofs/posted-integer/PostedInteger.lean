import Mathlib.Data.Nat.Prime.Basic

/-!
# A proper divisor of a 37-digit integer

Dominic Dabish independently found the factorization below. The integer also
appears in [a post by Tristan Lecourtois](https://x.com/tristanlecourt/status/2125763116017610869).
-/

namespace PostedInteger

def x : ℕ := 8193746205841170392658200302327406197

theorem factorization : x = 7 * 1170535172263024341808314328903915171 := rfl

theorem seven_dvd_x : 7 ∣ x := ⟨_, factorization⟩

theorem x_not_prime : ¬ Nat.Prime x :=
  Nat.not_prime_of_dvd_of_lt seven_dvd_x (by decide) (by decide)

end PostedInteger

#print axioms PostedInteger.factorization
#print axioms PostedInteger.x_not_prime
