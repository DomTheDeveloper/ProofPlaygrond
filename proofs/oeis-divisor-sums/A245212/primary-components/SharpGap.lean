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

end A245212SharpGap

#print axioms A245212SharpGap.finite_table
#print axioms A245212SharpGap.attained
