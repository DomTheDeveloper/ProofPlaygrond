import Mathlib.Data.Nat.Prime.Basic

/-! Arithmetic for the integer in Tristan Lecourtois's post. A disproof of the
named conjecture would also require the property this integer is claimed to violate.
https://x.com/tristanlecourt/status/2125763116017610869 -/

namespace PostedInteger

def x : ℕ := 8193746205841170392658200302327406197

theorem factorization : x = 7 * 1170535172263024341808314328903915171 := rfl

theorem seven_dvd_x : 7 ∣ x := ⟨_, factorization⟩

theorem x_not_prime : ¬ Nat.Prime x :=
  Nat.not_prime_of_dvd_of_lt seven_dvd_x (by decide) (by decide)

end PostedInteger
