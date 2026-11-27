import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# How much of the divisor-sum reply is determined by powers of two?

A midpoint m is locally possible at two if m²-N has a square root modulo
every power of two. We construct at least floor(sqrt(N)/2048) different
such integer midpoints in the real range for factors of ratio at most two.
We also verify the injective binary encoding used to measure ambiguous
answers and the floor-sum identity used to certify individual bits.
-/

namespace LocalBitCertificates

def LocallyPossible (n m : ℕ) : Prop :=
  ∀ k : ℕ, ∃ d : ZMod (2^k), (m : ZMod (2^k))^2 = (n : ZMod (2^k)) + d^2

def BalancedRange (n m : ℕ) : Prop := n ≤ m^2 ∧ 8*m^2 ≤ 9*n

private theorem odd_unit (k : ℕ) (x : ZMod (2^k)) : IsUnit (1+2*x) := by
  let s := 1+2*x.val
  have ho : Odd s := ⟨x.val, by dsimp [s]; omega⟩
  have hc : s.Coprime (2^k) := (Nat.coprime_two_right.mpr ho).pow_right _
  simpa [s] using (ZMod.isUnit_iff_coprime s _).mpr hc

private theorem quadratic_surj (k : ℕ) :
    Function.Surjective (fun x : ZMod (2^k) => x+2*x^2) := by
  apply Finite.injective_iff_surjective.mp
  intro x y h
  apply sub_eq_zero.mp
  apply (odd_unit k (x+y)).mul_left_eq_zero.mp
  calc
    (x-y)*(1+2*(x+y)) = (x+2*x^2)-(y+2*y^2) := by ring
    _ = 0 := sub_eq_zero.mpr h

/-- An explicit family of integer gaps which are squares at every dyadic precision. -/
theorem local_of_shape {n m j w : ℕ} (shape : m^2 = n+4^j*(8*w+1)) :
    LocallyPossible n m := by
  intro k
  obtain ⟨t, ht⟩ := quadratic_surj k (w : ZMod (2^k))
  refine ⟨2^j*(1+4*t), ?_⟩
  have he : (m : ZMod (2^k))^2 = n+4^j*(8*(w : ZMod (2^k))+1) := by
    exact_mod_cast congrArg (fun a : ℕ => (a : ZMod (2^k))) shape
  rw [he, ← ht, mul_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem residue_table : ∀ n : Fin 128, n.val%2=1 →
    ∃ r : Fin 64, ∃ j : Fin 3,
      r.val^2%(8*4^j.val) = (n.val+4^j.val)%(8*4^j.val) := by decide

private theorem square_reduces (m : ℕ) : m^2 ≡ (m%64)^2 [MOD 128] := by
  let r := m%64
  let t := m/64
  have e : m = r+64*t := (Nat.mod_add_div _ _).symm
  have eq : m^2 = r^2 + 128*(r*t+32*t^2) := by
    conv_lhs => rw [e]
    ring
  change m^2 % 128 = r^2 % 128
  rw [eq]
  simp

/-- One entire class modulo 64 survives every power of two, for each odd N. -/
theorem surviving_class {n : ℕ} (ho : n%2=1) :
    ∃ r < 64, ∀ m, m%64=r → n ≤ m^2 → LocallyPossible n m := by
  let a : Fin 128 := ⟨n%128, Nat.mod_lt _ (by decide)⟩
  have hodd : a.val%2=1 := by dsimp [a]; omega
  obtain ⟨r,j,ht⟩ := residue_table a hodd
  refine ⟨r.val,r.isLt,?_⟩
  intro m hr hm
  let f := 4^j.val
  let Q := 8*f
  have divides : Q ∣ 128 := by
    have : ∀ i : Fin 3, 8*4^i.val ∣ 128 := by decide
    exact this j
  have h₁ : m^2 ≡ r.val^2 [MOD Q] := by
    have h := (square_reduces m).of_dvd divides
    rwa [hr] at h
  have h₂ : a.val+f ≡ n+f [MOD Q] :=
    ((Nat.mod_modEq n 128).of_dvd divides).add_right f
  have eq : m^2 ≡ n+f [MOD Q] := (h₁.trans ht).trans h₂
  let d := m^2-n
  have hd : n+d=m^2 := by dsimp [d]; omega
  have hrem : d ≡ f [MOD Q] := Nat.ModEq.add_left_cancel' n (hd ▸ eq)
  have hf : 0 < f := by dsimp [f]; positivity
  have hfQ : f < Q := by dsimp [Q]; omega
  change d%Q=f%Q at hrem
  rw [Nat.mod_eq_of_lt hfQ] at hrem
  have hdiv := Nat.mod_add_div d Q
  rw [hrem] at hdiv
  apply local_of_shape (j:=j.val) (w:=d/Q)
  calc
    m^2 = n+d := hd.symm
    _ = n+(f+Q*(d/Q)) := congrArg (n+·) hdiv.symm
    _ = _ := by dsimp [Q, f]; ring

/-- Every index gives a different surviving midpoint in the balanced real interval. -/
theorem surviving_grid {n : ℕ} (ho : n%2=1) :
    ∃ g : Fin (n.sqrt/2048) → ℕ, Function.Injective g ∧
      ∀ i, BalancedRange n (g i) ∧ LocallyPossible n (g i) := by
  obtain ⟨r,hr,hs⟩ := surviving_class ho
  let t := n.sqrt
  let offset := (r+64-(t+1)%64)%64
  let g (i : Fin (n.sqrt/2048)) := t+1+offset+64*i.val
  refine ⟨g, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    dsimp [g] at h
    omega
  intro i
  have hi : i.val < t/2048 := i.isLt
  have hmod : (g i)%64 = r := by dsimp [g, offset]; omega
  have hlow : t+1 ≤ g i := by dsimp [g]; omega
  have htop : 32*g i ≤ 33*t := by dsimp [g, offset]; omega
  have hnlo : n ≤ (g i)^2 :=
    (Nat.lt_succ_sqrt' n).le.trans (Nat.pow_le_pow_left hlow _)
  have hb := Nat.pow_le_pow_left htop 2
  have ht : t^2 ≤ n := Nat.sqrt_le' n
  exact ⟨⟨hnlo, by nlinarith⟩, hs _ hmod hnlo⟩

/-- The parity of a nonnegative floor is a difference of floors. -/
theorem floor_parity (x n : ℕ) : (x/n)%2 + 2*(x/(2*n)) = x/n := by
  rw [Nat.mul_comm 2 n, ← Nat.div_div_eq_div_mul]
  exact Nat.mod_add_div _ _

/-- The exact number of ones over a progression, written without subtraction. -/
theorem progression_ones (count n a d : ℕ) :
    (∑ i ∈ Finset.range count, ((a*i+d)/n)%2) +
    2*(∑ i ∈ Finset.range count, (a*i+d)/(2*n)) =
    ∑ i ∈ Finset.range count, (a*i+d)/n := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => floor_parity _ _)

end LocalBitCertificates
