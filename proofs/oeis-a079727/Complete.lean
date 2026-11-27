import Block
import PriorProof

/-! A079727, Conjecture 4, via the two initial half-blocks.
The prime-field evaluation and the two initial congruences use eliayousf's
formalization. The interpolation and squarefree assembly are in Block.lean. -/

namespace Bala79727

private theorem initial_blocks {p : ℕ} (hp : OeisA3625.A p) :
    p ^ 2 ∣ block 0 (p / 2) ∧ p ^ 2 ∣ block p (p / 2) := by
  rcases eq_or_ne p 3 with rfl | h3
  · decide +kernel
  have hprime := hp.1
  have hres := hp.2
  have hgt : 3 < p := by have := hprime.two_le; omega
  have ev := OpenMath.A079727.prime_square_eval_zero hprime hgt hres
  constructor
  · simpa [block] using
      OpenMath.A079727.all_half_blocks_of_eval_zero hprime (by omega) 0 ev
  · simpa [block] using
      OpenMath.A079727.all_half_blocks_of_eval_zero hprime (by omega) 1 ev

/-- Peter Bala's squarefree-product congruence for A079727. -/
theorem conjecture4 (S : Finset ℕ) (hS : ∀ p ∈ S, OeisA3625.A p) :
    (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a (((∏ p ∈ S, p) - 1) / 2) := by
  have hprime (p) (hp : p ∈ S) : p.Prime ∧ 2 < p := by
    obtain ⟨h,hr⟩ := hS p hp
    exact ⟨h, by have := h.two_le; omega⟩
  simpa only [block, zero_add, Nat.centralBinom, OeisA79727.a] using
    squarefree_of_two_blocks S hprime (fun p hp => initial_blocks (hS p hp))

example : type_of% @OeisA79727.conjecture4 := Bala79727.conjecture4

#print axioms Bala79727.conjecture4

end Bala79727
