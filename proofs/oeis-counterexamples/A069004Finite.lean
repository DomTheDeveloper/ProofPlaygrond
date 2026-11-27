import Init

namespace A069004

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- For 3 ≤ q < 40000 any composite q has a proper divisor at most 199.
    Testing the gcd with (min (q-1) 199)! checks every such divisor. -/
def passes (q : Nat) : Bool :=
  Nat.gcd q (factorial (min (q - 1) 199) % q) == 1

/-- Multiply q + shift for the selected q = 4*j+3 in this dyadic block.
    The index j runs from k*2^d through (k+1)*2^d-1. -/
def block (shift : Nat) : Nat → Nat → Nat
  | 0, k =>
    let q := 4 * k + 3
    if q < 40000 && passes q then q + shift else 1
  | d + 1, k => block shift d (2 * k) * block shift d (2 * k + 1)

set_option maxHeartbeats 0 in
theorem product_bound : 16 * block 0 14 0 < 5 * block 1 14 0 := by
  decide +kernel

#print axioms product_bound

end A069004
