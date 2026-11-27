import Std

/-! Finite arithmetic for the even A245212 case with exactly one factor of 2
and two distinct odd prime divisors. The accompanying proof bounds the smaller
odd exponent by 36 and proves the final prime-power divisibility condition. -/

namespace A245212EvenTwo

private def terms (p : Nat) : Nat → Nat × Nat × Nat
  | 0 => (1, 1, 1)
  | a + 1 =>
    let (power, moment, sigma) := terms p a
    let next := power * p
    (next, moment + (a+2)*next, sigma + next)

/-- Once a power of q fails to divide the nonzero difference, all larger ones fail. -/
private def tailCheck (q T S scale delta : Nat) :
    Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => true
  | fuel+1, b, power, h, s =>
    if delta % power != 0 then true
    else
      let next := power*q
      decide (T*h + S*s ≠ scale*power*(b+1)) &&
        tailCheck q T S scale delta fuel (b+1) next (h+(b+2)*next) (s+next)

private def orientation (p q : Nat) : Bool :=
  (List.range 36).all fun j =>
    let a := j+1
    let (power, moment, sigma) := terms p a
    let T := 5*moment
    let S := 3*sigma
    let rhs := (q-1)*S
    let delta := max T rhs - min T rhs
    decide (0 < delta ∧ delta < 3^100) &&
      tailCheck q T S (8*power*(a+1)) delta 99 1 q (1+2*q) (1+q)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
theorem finite_certificate :
    ([5, 7, 11, 13] : List Nat).all (fun q =>
      orientation 3 q && orientation q 3) = true := by decide

end A245212EvenTwo

#print axioms A245212EvenTwo.finite_certificate
