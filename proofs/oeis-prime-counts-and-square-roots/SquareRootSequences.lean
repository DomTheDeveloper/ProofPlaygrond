module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace SquareRootSequences

/-- For positive n, its ceiling square root is one plus the floor square root of n-1. -/
theorem ceil_bounds {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    d = (n - 1).sqrt + 1 ↔ (d - 1)^2 < n ∧ n ≤ d^2 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
  have h : k = (n - 1).sqrt ↔ k^2 ≤ n - 1 ∧ n - 1 < (k+1)^2 := Nat.eq_sqrt'
  simp only [Nat.add_sub_cancel]
  omega

private theorem squareBand {v : ℕ} (hv : 0 < v) (k : ℕ) :
    (k^2 < v * (k+1) ∧ v * (k+1) ≤ (k+1)^2) ↔ v = k ∨ v = k+1 := by
  constructor
  · rintro ⟨hl, hu⟩
    have hu' : v ≤ k+1 := Nat.le_of_mul_le_mul_right
      (by simpa only [pow_two] using hu) (Nat.succ_pos k)
    by_cases h : k ≤ v
    · omega
    · have hp := Nat.mul_le_mul_right (k+1) (show v+1 ≤ k by omega)
      nlinarith only [hl, hp]
  · rintro (rfl | rfl) <;> constructor <;> nlinarith

/-- A069187. The squarefree part is expressed by the unique decomposition
n = m²*d with squarefree d. The isolated solution n=1 is essential. -/
theorem squarefree_ceiling {n : ℕ} (hn : 0 < n) :
    (∃ m d : ℕ, Squarefree d ∧ n = m^2*d ∧ d = (n-1).sqrt+1) ↔
      n = 1 ∨ ∃ m : ℕ, 0 < m ∧ Squarefree (m^2+1) ∧ n = m^2*(m^2+1) := by
  constructor
  · rintro ⟨m, d, hs, he, hc⟩
    have hm : 0 < m := by
      by_contra! h
      have : m = 0 := by omega
      simp [this] at he
      omega
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k+1 := ⟨(n-1).sqrt, hc⟩
    have hb := (ceil_bounds hn (Nat.succ_pos k)).mp hc
    rw [he] at hb
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one] at hb
    rcases (squareBand (pow_pos hm 2) k).mp hb with hk | hk
    · right
      exact ⟨m, hm, hk.symm ▸ hs, by simpa only [hk] using he⟩
    · have hdiv : m*m ∣ k+1 := by rw [← hk, pow_two]
      have hm1 : m = 1 := Nat.isUnit_iff.mp (hs m hdiv)
      left
      simpa [← hk, hm1] using he
  · rintro (rfl | ⟨m, hm, hs, rfl⟩)
    · exact ⟨1, 1, squarefree_one, rfl, rfl⟩
    · refine ⟨m, m^2+1, hs, rfl, (ceil_bounds hn (Nat.succ_pos _)).mpr ?_⟩
      simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        (squareBand (pow_pos hm 2) (m^2)).mpr (Or.inl rfl)

/-- The proposed formula without the isolated 1 has a counterexample at 1. -/
theorem squarefree_literal_false :
    ¬ (∀ n : ℕ, 0 < n →
      ((∃ m d : ℕ, Squarefree d ∧ n = m^2*d ∧ d = (n-1).sqrt+1) ↔
       ∃ m : ℕ, 0 < m ∧ Squarefree (m^2+1) ∧ n = m^2*(m^2+1))) := by
  intro hall
  obtain ⟨m, hm, _, he⟩ := (hall 1 (Nat.zero_lt_succ 0)).mp
    ⟨1, 1, squarefree_one, rfl, rfl⟩
  have hm2 : 0 < m^2 := pow_pos hm 2
  have H := Nat.mul_le_mul_right (m^2+1) (show 1 ≤ m^2 by omega)
  simp only [one_mul] at H
  omega

/-- A034097. The first fractional decimal digit of the square root is one
in the k-th block exactly when floor(10*sqrt(n)) = 10*k+1. -/
theorem digit_one_block (k n : ℕ) :
    10*k+1 = (100*n).sqrt ↔ k*k + k/5 < n ∧ n ≤ k*k + (2*k)/5 := by
  rw [Nat.eq_sqrt]
  rw [show (10*k+1)*(10*k+1) = 100*(k*k)+20*k+1 by ring,
      show (10*k+1+1)*(10*k+1+1) = 100*(k*k)+40*k+4 by ring]
  omega

/-- The right side is floor(1/2 + 1/25 + k/5), the stated nearest integer. -/
theorem digit_one_run_length (k : ℕ) :
    (2*k)/5 - k/5 = (10*k+27)/50 := by
  have hm := Nat.mod_add_div k 5
  have hr : k%5 = 0 ∨ k%5 = 1 ∨ k%5 = 2 ∨ k%5 = 3 ∨ k%5 = 4 := by omega
  rcases hr with h | h | h | h | h <;> omega

/-- The intervening square (k+1)² separates two successive nonempty blocks. -/
theorem digit_one_gap (k : ℕ) : k*k + (2*k)/5 < (k+1)*(k+1) := by
  rw [show (k+1)*(k+1) = k*k+2*k+1 by ring]
  omega

private theorem digit_member (n : ℕ) :
    (100*n).sqrt % 10 = 1 ↔
      n.sqrt*n.sqrt+n.sqrt/5 < n ∧ n ≤ n.sqrt*n.sqrt+(2*n.sqrt)/5 := by
  constructor
  · intro hd
    let k := (100*n).sqrt/10
    have he : 10*k+1 = (100*n).sqrt := by dsimp [k]; omega
    obtain ⟨ha,hb⟩ := (digit_one_block k n).mp he
    have gap := digit_one_gap k
    have hroot : k = n.sqrt := Nat.eq_sqrt.mpr ⟨by omega, by omega⟩
    simpa only [← hroot] using And.intro ha hb
  · intro h
    have he := (digit_one_block n.sqrt n).mpr h
    omega

/-- The maximal run containing n, with both neighbours, the entire interval
and its exact rounded length. All digit tests use the standard Nat.sqrt. -/
theorem digit_one_maximal_run : ∀ n : ℕ, (100*n).sqrt % 10 = 1 →
    ∃ lo hi : ℕ, 0 < lo ∧ lo ≤ n ∧ n ≤ hi ∧
      (∀ j : ℕ, lo ≤ j → j ≤ hi → (100*j).sqrt % 10 = 1) ∧
      (100*(lo-1)).sqrt % 10 ≠ 1 ∧ (100*(hi+1)).sqrt % 10 ≠ 1 ∧
      hi+1-lo = (10*n.sqrt+27)/50 := by
  intro n h
  let k := n.sqrt
  obtain ⟨ha,hb⟩ := (digit_member n).mp h
  change k*k+k/5 < n at ha
  change n ≤ k*k+(2*k)/5 at hb
  have hk : 0 < k := by
    by_contra! hz
    have h0 : k = 0 := by omega
    simp [h0] at ha hb
    omega
  have gap : k*k+(2*k)/5+1 < (k+1)*(k+1) := by
    rw [show (k+1)*(k+1) = k*k+2*k+1 by ring]
    omega
  have hrootA : k = (k*k+k/5).sqrt := Nat.eq_sqrt.mpr ⟨by omega, by omega⟩
  have hrootB : k = (k*k+(2*k)/5+1).sqrt := Nat.eq_sqrt.mpr ⟨by omega, gap⟩
  refine ⟨k*k+k/5+1, k*k+(2*k)/5, by omega, by omega, hb, ?_, ?_, ?_, ?_⟩
  · intro j hj1 hj2
    have he := (digit_one_block k j).mpr ⟨by omega, hj2⟩
    omega
  · rw [Nat.add_sub_cancel]
    intro hd
    have hx := ((digit_member _).mp hd).1
    rw [← hrootA] at hx
    omega
  · intro hd
    have hx := ((digit_member _).mp hd).2
    rw [← hrootB] at hx
    omega
  · change _ = (10*k+27)/50
    have hlen := digit_one_run_length k
    omega

#print axioms squarefree_literal_false
#print axioms digit_one_maximal_run
#print axioms squarefree_ceiling
#print axioms digit_one_block
#print axioms digit_one_run_length
#print axioms digit_one_gap

end SquareRootSequences
