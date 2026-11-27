import Std

/-! Direct finite-field certificates for the first Bala congruence level.
The written proof shows why the finite sum for a prime controls every multiplier. -/

namespace BalaObstruction

private def bin (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => bin n k * (n-k) / (k+1)

private def seed (offset n : Nat) : Nat :=
  (List.range n).foldl (fun v k =>
    v + bin n k * bin (n-1) k * bin (n+k-1+offset) k) 0

private def obstruction (p offset : Nat) : Nat :=
  ((List.range (p-1)).foldl (fun v i =>
    let s := i+1
    (v + (seed offset s % p) * (seed offset (p-s) % p) * (s^(p-3) % p)) % p) 0)

set_option maxRecDepth 14000 in
set_option maxHeartbeats 4000000 in
theorem obstruction_table :
    ([7,11,13,17,19,23,29,31] : List Nat).all
      (fun p => decide (obstruction p 0 = 0 ∧ obstruction p 1 = 0)) = true := by
  decide

theorem prime_five : obstruction 5 0 = 3 ∧ obstruction 5 1 = 2 := by decide

end BalaObstruction

#print axioms BalaObstruction.obstruction_table
#print axioms BalaObstruction.prime_five
