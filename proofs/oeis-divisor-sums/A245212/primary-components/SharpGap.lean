import Std

/-!
Exact finite arithmetic for the four-prime gap in the accompanying proof.
The second prime is 5 or 7, the third is at most 31, and the last has
a linear upper bound whenever the product on the first three is below 2.
-/

namespace A245212SharpGap

def rows : List (Nat × Nat) :=
  [(5, 7), (5, 11), (5, 13), (5, 17), (5, 19), (5, 23), (5, 29),
   (5, 31), (7, 11), (7, 13)]

/-- Every composite at most 256 has a divisor in this interval. -/
def primeThrough256 (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range 15).all fun i => decide (i + 2 = n) || n % (i + 2) != 0

def checkRow (row : Nat × Nat) : Bool := Id.run do
  let (p, q) := row
  let u := 3 * p * q
  let v := 2 * (p - 1) * (q - 1)
  if 2 * v < u then return decide (12801 * v ≤ 6400 * u)
  if 2 * v = u then return false
  let last := (2 * v - 1) / (2 * v - u)
  if 256 < last then return false
  return (List.range (last + 1)).all fun r =>
    decide (r ≤ q) || !primeThrough256 r || decide (u * r ≤ 2 * v * (r - 1)) ||
      decide (12801 * v * (r - 1) ≤ 6400 * u * r)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem finite_table : rows.all checkRow = true := by decide

theorem attained :
    primeThrough256 251 = true ∧
      6400 * (3 * 5 * 17 * 251 : Nat) = 12801 * (2 * 4 * 16 * 250) := by decide

/-- The local weighted divisor sum at a prime power of exponent e. -/
def weighted (p : Nat) : Nat → Nat
  | 0 => 1
  | e + 1 => weighted p e + (e + 2) * p ^ (e + 1)

/-- The local weighted sum at any odd fourth power is odd. -/
theorem fourth_power_odd (p : Nat) (hp : p % 2 = 1) (k : Nat) :
    weighted p (4 * k) % 2 = 1 := by
  have powmod (j : Nat) : p ^ j % 2 = 1 := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Nat.pow_succ, Nat.mul_mod, ih, hp]
  have step (e : Nat) :
      weighted p (e + 1) % 2 = (weighted p e + (e + 2)) % 2 := by
    rw [weighted, Nat.add_mod, Nat.mul_mod, powmod, Nat.mul_one, Nat.mod_mod,
      ← Nat.add_mod]
  have split (e : Nat) : weighted p (e + 1) % 2 =
      (weighted p e % 2 + (e + 2) % 2) % 2 :=
    (step e).trans (Nat.add_mod _ _ _)
  induction k with
  | zero => rfl
  | succ k ih =>
    have h₁ : weighted p (4 * k + 1) % 2 = 1 := by
      rw [split, ih, show (4 * k + 2) % 2 = 0 by omega]
    have h₂ : weighted p (4 * k + 2) % 2 = 0 := by
      rw [split (4 * k + 1), h₁, show (4 * k + 1 + 2) % 2 = 1 by omega]
    have h₃ : weighted p (4 * k + 3) % 2 = 0 := by
      rw [split (4 * k + 2), h₂, show (4 * k + 2 + 2) % 2 = 0 by omega]
    rw [Nat.mul_succ, split (4 * k + 3), h₃, show (4 * k + 3 + 2) % 2 = 1 by omega]

end A245212SharpGap

#print axioms A245212SharpGap.finite_table
#print axioms A245212SharpGap.attained
#print axioms A245212SharpGap.fourth_power_odd
