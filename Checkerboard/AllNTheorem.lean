import Checkerboard.AllNUpper
import Checkerboard.N6Explicit

/-!
# Complete all-n checkerboard upper bound
-/

namespace Checkerboard

/-- For every `n ≥ 6`, every no-three-in-line subset of either checkerboard
color class has at most `2n-4` points. -/
theorem checkerboard_upper_all_n {n parity : ℕ}
    (hn : 6 ≤ n) (hp : parity = 0 ∨ parity = 1)
    (s : Finset (Point n))
    (hcolor : Monochromatic parity s) (hntil : NoThreeInLine s) :
    s.card ≤ 2 * n - 4 := by
  by_cases h6 : n = 6
  · subst n
    rcases hp with rfl | rfl
    · exact n6_zero_upper s hcolor hntil
    · exact n6_one_upper s hcolor hntil
  · exact checkerboard_upper_from_seven (n := n) (parity := parity)
      (s := s) (by omega) hp hcolor hntil

end Checkerboard
