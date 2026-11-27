import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A short separating block in a doubling orbit

A bad multiplier has a nonzero relation a*x = y modulo n with 1 <= x <= W
and 0 < |y| <= H. For the factoring application the multiplier is a power
of two modulo an odd n, so a zero residue is impossible when W < n.
-/

namespace DoublingWindow

structure Relation (n a W H x y : ℤ) : Prop where
  xpos : 0 < x
  width : x ≤ W
  ypos : 0 < |y|
  height : |y| ≤ H
  congruence : n ∣ a*x-y

private theorem product_bound {W H x y : ℤ} (hx : 0 ≤ x) (hxW : x ≤ W)
    (hy : |y| ≤ H) : |y*x| ≤ W*H := by
  rw [abs_mul, abs_of_nonneg hx, mul_comm W H]
  exact mul_le_mul hy hxW hx (by linarith [abs_nonneg y])

/-- Two nearby relations at consecutive exponents have zero integer determinant. -/
theorem consecutive {n a W H x y z v : ℤ} (hn : 0 < n) (small : 3*W*H < n)
    (first : Relation n a W H x y) (second : Relation n (2*a) W H z v) :
    v*x=2*y*z := by
  obtain ⟨k,hk⟩ := first.congruence
  obtain ⟨l,hl⟩ := second.congruence
  have hy : y=a*x-n*k := by linarith
  have hv : v=2*a*z-n*l := by linarith
  have eq : v*x-2*y*z = n*(2*k*z-l*x) := by rw [hy,hv]; ring
  have hxv := abs_le.mp (product_bound first.xpos.le first.width second.height)
  have hzy := abs_le.mp (product_bound second.xpos.le second.width first.height)
  have hsmall : |v*x-2*y*z| < n := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  by_contra bad
  have hne : 2*k*z-l*x ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at eq
    exact bad (sub_eq_zero.mp eq)
  have hpos := abs_pos.mpr hne
  have hlower : (1:ℤ) ≤ |2*k*z-l*x| := by omega
  rw [eq,abs_mul,abs_of_pos hn] at hsmall
  nlinarith [mul_le_mul_of_nonneg_left hlower hn.le]

/-- By this many doublings there is a multiplier with no short nonzero relation. -/
theorem exists_separating_shift (n a W H : ℕ) (hn : 0 < n) (small : 3*W*H < n) :
    ∃ i ≤ (W*H).size, ¬ ∃ x y : ℤ, Relation (n:ℤ) ((a:ℤ)*2^i) W H x y := by
  classical
  let T := (W*H).size
  by_contra! every
  obtain ⟨x₀,y₀,h₀⟩ := every 0 (Nat.zero_le _)
  have chain : ∀ i ≤ T, ∃ x y : ℤ, Relation (n:ℤ) ((a:ℤ)*2^i) W H x y ∧
      y*x₀ = 2^i*y₀*x := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨x₀,y₀,h₀,by ring⟩
    | succ i ih =>
      intro hi
      obtain ⟨x,y,h,eq⟩ := ih (by omega)
      obtain ⟨z,v,h'⟩ := every (i+1) hi
      have mult : (a:ℤ)*2^(i+1) = 2*((a:ℤ)*2^i) := by rw [pow_succ]; ring
      have h'2 := h'
      rw [mult] at h'2
      have det := consecutive (by exact_mod_cast hn) (by exact_mod_cast small) h h'2
      refine ⟨z,v,h',?_⟩
      apply mul_right_cancel₀ h.xpos.ne'
      calc
        v*x₀*x = (v*x)*x₀ := by ring
        _ = (2*y*z)*x₀ := by rw [det]
        _ = 2*z*(y*x₀) := by ring
        _ = 2*z*(2^i*y₀*x) := by rw [eq]
        _ = 2^(i+1)*y₀*z*x := by rw [pow_succ]; ring
  obtain ⟨x,y,h,eq⟩ := chain T le_rfl
  have upper := product_bound h₀.xpos.le h₀.width h.height
  have h₁ : (1:ℤ) ≤ |y₀| := h₀.ypos
  have h₂ : (1:ℤ) ≤ x := h.xpos
  have lower : (2:ℤ)^T ≤ |2^T*y₀*x| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (2:ℤ)^T by positivity), abs_of_pos h.xpos]
    have e := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ (2:ℤ)^T by positivity)
    have f := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (2:ℤ)^T*|y₀| by positivity)
    simpa using (by nlinarith : (2:ℤ)^T ≤ (2:ℤ)^T * |y₀| * x)
  have strict : (W:ℤ)*H < 2^T := by exact_mod_cast Nat.lt_size_self (W*H)
  rw [← eq] at lower
  omega

/-- Equal quantization bins imply a short ordinary difference between residues. -/
theorem equal_bin_narrow {n P r s : ℕ} (hn : 0 < n) (hP : 0 < P)
    (hr : 0 < r) (hrs : r ≤ s) (same : (P*r-1)/n=(P*s-1)/n) :
    s-r ≤ (n-1)/P := by
  have hp₁ : 0 < P*r := Nat.mul_pos hP hr
  have hp₂ : 0 < P*s := Nat.mul_pos hP (lt_of_lt_of_le hr hrs)
  have eb := Nat.mod_add_div (P*r-1) n
  have ec := Nat.mod_add_div (P*s-1) n
  rw [same] at eb
  have hb := Nat.mod_lt (P*s-1) hn
  apply (Nat.le_div_iff_mul_le hP).mpr
  rw [Nat.mul_comm, Nat.mul_sub]
  omega

def leftFloor (n r j : ℕ) := (2^j*r-1)/n

/-- Read consecutive replies in order, most significant bit first. -/
def word (n r start : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => 2*word n r start h + leftFloor n r (start+h+1)%2

private theorem floor_double {n r : ℕ} (hr : 0 < r) (j : ℕ) :
    leftFloor n r (j+1)/2=leftFloor n r j := by
  let v := 2^j*r
  have hv : 0 < v := Nat.mul_pos (Nat.two_pow_pos _) hr
  unfold leftFloor
  rw [Nat.div_div_eq_div_mul, mul_comm n 2, ← Nat.div_div_eq_div_mul]
  have e : 2^(j+1)*r = 2*v := by dsimp [v]; rw [pow_succ]; ring
  rw [e]
  have : (2*v-1)/2 = v-1 := by omega
  rw [this]

theorem word_eq_mod {n r : ℕ} (hr : 0 < r) (start h : ℕ) :
    word n r start h = leftFloor n r (start+h)%2^h := by
  induction h with
  | zero => simp [word, Nat.mod_one]
  | succ h ih =>
    rw [word, ih, pow_succ', Nat.mod_mul]
    simp only [Nat.add_succ]
    rw [floor_double hr]
    simp only [Nat.add_zero]
    omega

private def rep (n A m : ℕ) := (A*(1+2*m)-1)%n+1

private theorem rep_split {n A : ℕ} (hA : 0 < A) (m : ℕ) :
    A*(1+2*m) = rep n A m + n*((A*(1+2*m)-1)/n) := by
  have pos : 0 < A*(1+2*m) := by positivity
  have := Nat.mod_add_div (A*(1+2*m)-1) n
  dsimp [rep]
  omega

private theorem word_eq_cell {n : ℕ} (hn : 0 < n) (m j h : ℕ) :
    word n (1+2*m) j h = (2^h*rep n (2^j) m-1)/n := by
  rw [word_eq_mod (by omega), leftFloor]
  let A := 2^j
  let P := 2^h
  let r := rep n A m
  let q := (A*(1+2*m)-1)/n
  have hp : 0<P := Nat.two_pow_pos _
  have hr : 0<r := Nat.succ_pos _
  have hrn : r ≤ n := Nat.mod_lt _ hn
  have e : A*(1+2*m)=r+n*q := rep_split (Nat.two_pow_pos _) _
  have e' : 2^(j+h)*(1+2*m) = P*r+n*(P*q) := calc
    _ = P*(A*(1+2*m)) := by dsimp [P,A]; rw [pow_add]; ring
    _ = _ := by rw [e]; ring
  have hpr : 0<P*r := Nat.mul_pos hp hr
  have lt : (P*r-1)/n < P := (Nat.div_lt_iff_lt_mul hn).mpr
    (by have := Nat.mul_le_mul_left P hrn; omega)
  rw [e', show P*r+n*(P*q)-1=(P*r-1)+n*(P*q) by omega, Nat.add_mul_div_left _ _ hn]
  change ((P*r-1)/n+P*q)%P = (P*r-1)/n
  simpa using Nat.mod_eq_of_lt lt

private theorem different_words {n W m d j h : ℕ} (hn : 0 < n) (hd : 0<d)
    (hdW : d ≤ W) (hW : W < n) (oddN : Odd n)
    (sep : ¬ ∃ x y : ℤ,
      Relation n (2*(2:ℤ)^j) W (((n-1)/2^h : ℕ) : ℤ) x y) :
    word n (1+2*m) j h ≠ word n (1+2*(m+d)) j h := by
  intro eq
  rw [word_eq_cell hn, word_eq_cell hn] at eq
  let A := 2^j
  let r := rep n A m
  let s := rep n A (m+d)
  let q := (A*(1+2*m)-1)/n
  let t := (A*(1+2*(m+d))-1)/n
  have e₁ : A*(1+2*m)=r+n*q := rep_split (Nat.two_pow_pos _) _
  have e₂ : A*(1+2*(m+d))=s+n*t := rep_split (Nat.two_pow_pos _) _
  have z₁ : (A:ℤ)*(1+2*m)=r+(n:ℤ)*q := by exact_mod_cast e₁
  have z₂ : (A:ℤ)*(1+2*((m:ℤ)+d))=s+(n:ℤ)*t := by exact_mod_cast e₂
  have dv : (n:ℤ) ∣ 2*(A:ℤ)*(d:ℤ)-((s:ℤ)-r) := by
    refine ⟨(t:ℤ)-q,?_⟩
    nlinarith only [z₁,z₂]
  have ne : (s:ℤ)-r ≠ 0 := by
    intro hz
    rw [hz,sub_zero] at dv
    have dvd : n ∣ 2*A*d := by exact_mod_cast dv
    have hc := Nat.coprime_two_left.mpr oddN
    have hnd := (hc.mul_left (hc.pow_left j)).symm.dvd_of_dvd_mul_left dvd
    have := Nat.le_of_dvd hd hnd
    omega
  have hr : 0<r := Nat.succ_pos _
  have hs : 0<s := Nat.succ_pos _
  have bound : |(s:ℤ)-r| ≤ (((n-1)/2^h : ℕ) : ℤ) := by
    rw [abs_le]
    rcases le_total r s with h₁ | h₁
    · have := equal_bin_narrow hn (Nat.two_pow_pos _) hr h₁ eq
      omega
    · have := equal_bin_narrow hn (Nat.two_pow_pos _) hs h₁ eq.symm
      omega
  exact sep ⟨d,(s:ℤ)-r,⟨by exact_mod_cast hd,by exact_mod_cast hdW,abs_pos.mpr ne,bound,
    by exact_mod_cast dv⟩⟩

/-- At some computably bounded starting index the observed word is injective on
every interval of midpoints of width W, provided the number of cells exceeds 3W. -/
theorem short_word_separates {n W h : ℕ} (hn : 0<n) (oddN : Odd n)
    (hW : W<n) (cells : 3*W < 2^h) (base : ℕ) :
    ∃ i ≤ (W*((n-1)/2^h)).size, ∀ m d, 0<d → d≤W →
      word n (1+2*m) (base+i) h ≠ word n (1+2*(m+d)) (base+i) h := by
  let H := (n-1)/2^h
  have small : 3*W*H<n := calc
    _ ≤ 2^h*H := Nat.mul_le_mul_right H cells.le
    _ ≤ n-1 := Nat.mul_div_le _ _
    _ < n := by omega
  obtain ⟨i,hi,good⟩ := exists_separating_shift n (2*2^base) W H hn small
  refine ⟨i, hi, ?_⟩
  intro m d hd hdW
  apply different_words hn hd hdW hW oddN
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add,mul_assoc,H] using good

end DoublingWindow
