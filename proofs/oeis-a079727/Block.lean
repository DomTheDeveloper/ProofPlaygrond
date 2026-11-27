module

public import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Bala79727

/-- Sum of a block of central binomial cubes, including both endpoints. -/
def block (b r : ℕ) : ℕ := ∑ i ∈ Finset.range (r + 1), (b + i).centralBinom ^ 3

private def denominator (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => denominator b r * (b + r + 1)^3

private def topTerm (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => topTerm b r * (2 * (2 * (b + r) + 1))^3

private def numerator (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => numerator b r * (b + r + 1)^3 + topTerm b (r + 1)

private theorem clear_term (b r : ℕ) :
    denominator b r * (b + r).centralBinom ^ 3 = b.centralBinom ^ 3 * topTerm b r := by
  induction r with
  | zero => simp [denominator, topTerm]
  | succ r ih =>
    have hc := congrArg (fun x : ℕ => x^3) (Nat.succ_mul_centralBinom_succ (b+r))
    simp only [mul_pow] at hc
    simp only [denominator, topTerm, ← Nat.add_assoc] at *
    calc
      _ = denominator b r * ((b+r+1)^3 * (b+r+1).centralBinom^3) := by ring
      _ = _ := by rw [hc, ← mul_assoc (b.centralBinom^3), ← ih]; ring

private theorem clear_block (b r : ℕ) :
    denominator b r * block b r = b.centralBinom ^ 3 * numerator b r := by
  induction r with
  | zero => simp [denominator, block, numerator]
  | succ r ih =>
    have hb : block b (r+1) = block b r + (b+(r+1)).centralBinom^3 :=
      Finset.sum_range_succ _ _
    rw [hb, Nat.mul_add, clear_term, numerator, denominator, Nat.mul_add]
    rw [← mul_assoc (b.centralBinom^3), ← ih]
    ring

private def Affine (p : ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ u v : ZMod (p^2), ∀ j : ℕ, (f (j*p) : ZMod (p^2)) = u + (j : ZMod (p^2)) * (p : ZMod (p^2)) * v

private theorem affine_const (p n : ℕ) : Affine p (fun _ => n) :=
  ⟨n, 0, by simp⟩

private theorem affine_id (p : ℕ) : Affine p (fun n => n) :=
  ⟨0, 1, by simp⟩

private theorem Affine.add {p : ℕ} {f g : ℕ → ℕ} (hf : Affine p f) (hg : Affine p g) :
    Affine p (fun b => f b + g b) := by
  obtain ⟨u,v,h⟩ := hf
  obtain ⟨w,s,k⟩ := hg
  exact ⟨u+w, v+s, fun j => by simp only [Nat.cast_add, h, k]; ring⟩

private theorem Affine.mul {p : ℕ} {f g : ℕ → ℕ} (hf : Affine p f) (hg : Affine p g) :
    Affine p (fun b => f b * g b) := by
  obtain ⟨u,v,h⟩ := hf
  obtain ⟨w,s,k⟩ := hg
  have hp : (p : ZMod (p^2))^2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  refine ⟨u*w,u*s+v*w,fun j => ?_⟩
  simp only [Nat.cast_mul, h, k]
  calc
    _ = u*w + (j : ZMod (p^2))*(p : ZMod (p^2))*(u*s+v*w) + (j : ZMod (p^2))^2*(p : ZMod (p^2))^2*v*s := by ring
    _ = _ := by rw [hp]; ring

private theorem Affine.cube {p : ℕ} {f : ℕ → ℕ} (hf : Affine p f) :
    Affine p (fun b => f b ^ 3) := by
  simpa only [pow_succ, pow_zero, one_mul] using (hf.mul hf).mul hf

private theorem numerator_affine (p r : ℕ) : Affine p (fun b => numerator b r) := by
  suffices ∀ i, Affine p (fun b => topTerm b i) ∧ Affine p (fun b => numerator b i) from (this r).2
  intro i
  induction i with
  | zero => exact ⟨affine_const p 1, affine_const p 1⟩
  | succ i ih =>
    have hb := (affine_id p).add (affine_const p i)
    have htop := ih.1.mul (((affine_const p 2).mul
      (((affine_const p 2).mul hb).add (affine_const p 1))).cube)
    exact ⟨htop, (ih.2.mul ((hb.add (affine_const p 1)).cube)).add htop⟩

private theorem affine_vanish {p : ℕ} {f : ℕ → ℕ} (hf : Affine p f)
    (h0 : p^2 ∣ f 0) (h1 : p^2 ∣ f p) (j : ℕ) : p^2 ∣ f (j*p) := by
  obtain ⟨u,v,h⟩ := hf
  have hz := (ZMod.natCast_eq_zero_iff _ _).2 h0
  have ho := (ZMod.natCast_eq_zero_iff _ _).2 h1
  have hu : u = 0 := by simpa [hz] using (h 0).symm
  have hv : (p : ZMod (p^2))*v = 0 := by simpa [hu,ho] using (h 1).symm
  apply (ZMod.natCast_eq_zero_iff _ _).1
  rw [h, hu, zero_add, mul_assoc, hv, mul_zero]


private theorem coprime_denominator {p : ℕ} (hp : p.Prime) (j r : ℕ) (hr : r < p) :
    (p^2).Coprime (denominator (j*p) r) := by
  apply Nat.Coprime.pow_left
  induction r with
  | zero => simp [denominator]
  | succ r ih =>
    apply Nat.Coprime.mul_right (ih (by omega))
    apply Nat.Coprime.pow_right
    apply hp.coprime_iff_not_dvd.mpr
    have hmod : (j*p+r+1)%p = r+1 := by
      rw [Nat.add_assoc, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]
    intro h
    rw [Nat.mod_eq_zero_of_dvd h] at hmod
    omega

private theorem coprime_central_prime {p : ℕ} (hp : p.Prime) (hodd : 2 < p) :
    (p^2).Coprime (p.centralBinom^3) := by
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.pow_right
  apply hp.coprime_iff_not_dvd.mpr
  let : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_mul_mul_modEq_choose_nat (p := p) (a := 2) (b := 1)
  have h' : p.centralBinom % p = 2 := by
    simpa [Nat.centralBinom, Nat.ModEq, Nat.mul_comm p 2, Nat.mod_eq_of_lt hodd] using h
  intro hd
  rw [Nat.mod_eq_zero_of_dvd hd] at h'
  contradiction

/-- Two initial block sums control every translate by a multiple of the prime. -/
theorem block_lift {p : ℕ} (hp : p.Prime) (hodd : 2 < p) (r : ℕ) (hr : r < p)
    (h0 : p^2 ∣ block 0 r) (h1 : p^2 ∣ block p r) (j : ℕ) :
    p^2 ∣ block (j*p) r := by
  have hzero : p^2 ∣ numerator 0 r := by
    simpa [clear_block] using (dvd_mul_of_dvd_right h0 (denominator 0 r))
  have hone : p^2 ∣ numerator p r := by
    apply (coprime_central_prime hp hodd).dvd_mul_left.mp
    rw [← clear_block]
    exact dvd_mul_of_dvd_right h1 _
  apply (coprime_denominator hp j r hr).dvd_mul_left.mp
  rw [clear_block]
  exact dvd_mul_of_dvd_right (affine_vanish (numerator_affine p r) hzero hone j) _

private theorem total_blocks {p h : ℕ}
    (hfull : ∀ j, p^2 ∣ block (j*p) (p-1))
    (hhalf : ∀ j, p^2 ∣ block (j*p) h) (hp : 0 < p) (j : ℕ) :
    p^2 ∣ block 0 (j*p+h) := by
  let f := fun i : ℕ => i.centralBinom^3
  have pre (k : ℕ) : p^2 ∣ ∑ i ∈ Finset.range (k*p), f i := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add]
      apply dvd_add ih
      simpa [block, Nat.sub_add_cancel hp, f] using hfull k
  have hh := dvd_add (pre j) (hhalf j)
  simpa [block, ← Finset.sum_range_add, Nat.add_assoc, f] using hh

/-- A pair of finite certificates for both block lengths implies divisibility
at every index of the form $(mp-1)/2$ with $m$ odd. -/
theorem prime_square_dvd {p m : ℕ} (hp : p.Prime) (hodd : 2 < p) (hm : Odd m)
    (h0 : p^2 ∣ block 0 (p/2)) (h1 : p^2 ∣ block p (p/2))
    (hf0 : p^2 ∣ block 0 (p-1)) (hf1 : p^2 ∣ block p (p-1)) :
    p^2 ∣ block 0 ((m*p-1)/2) := by
  obtain ⟨j,rfl⟩ := hm
  have hpar := hp.odd_of_ne_two (by omega)
  obtain ⟨l,hl⟩ := hpar
  have hidx : ((2*j+1)*p-1)/2 = j*p+p/2 := by
    rw [show (2*j+1)*p = 2*(j*p)+p by ring]
    omega
  rw [hidx]
  exact total_blocks (block_lift hp hodd _ (by omega) hf0 hf1)
    (block_lift hp hodd _ (by omega) h0 h1) hp.pos j

private theorem tail_dvd {p r : ℕ} (hp : p.Prime) (j : ℕ)
    (hlo : p/2 < r) (hhi : r < p) : p^2 ∣ (j*p+r).centralBinom^3 := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := 2*(j*p+r)) (k := j*p+r)
  have hr : (j*p+r)%p = r := by simp [Nat.mod_eq_of_lt hhi]
  have htop : (2*(j*p+r))%p = 2*r-p := by
    rw [show 2*(j*p+r) = (2*j+1)*p+(2*r-p) by
      rw [Nat.add_mul, one_mul, Nat.mul_add, ← Nat.mul_assoc]; omega]
    simp [Nat.mod_eq_of_lt (show 2*r-p < p by omega)]
  rw [hr, htop, Nat.choose_eq_zero_of_lt (show 2*r-p < r by omega), zero_mul] at hc
  have hd : p ∣ (j*p+r).centralBinom := Nat.modEq_zero_iff_dvd.mp hc
  exact dvd_trans (pow_dvd_pow_of_dvd hd 2) (pow_dvd_pow _ (by decide : 2 ≤ 3))

private theorem full_of_half {p : ℕ} (hp : p.Prime) (j : ℕ)
    (hh : p^2 ∣ block (j*p) (p/2)) : p^2 ∣ block (j*p) (p-1) := by
  have hpos := hp.two_le
  have len : p-1+1 = (p/2+1) + (p-(p/2+1)) := by omega
  unfold block at *
  rw [len, Finset.sum_range_add]
  refine dvd_add hh (Finset.dvd_sum fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  exact tail_dvd hp j (by omega) (by omega)

/-- The first two half-block sums suffice for every odd multiple of the prime. -/
theorem odd_multiple_of_two_blocks {p m : ℕ} (hp : p.Prime) (hodd : 2 < p) (hm : Odd m)
    (h0 : p^2 ∣ block 0 (p/2)) (h1 : p^2 ∣ block p (p/2)) :
    p^2 ∣ block 0 ((m*p-1)/2) := by
  apply prime_square_dvd hp hodd hm h0 h1
  · simpa using full_of_half hp 0 (by simpa using h0)
  · simpa using full_of_half hp 1 (by simpa using h1)

private theorem product_dvd {S : Finset ℕ} {N : ℕ}
    (hs : ∀ p ∈ S, Nat.Prime p) (hd : ∀ p ∈ S, p^2 ∣ N) :
    (∏ p ∈ S, p)^2 ∣ N := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp := hs p (Finset.mem_insert_self ..)
    have hq (q) (hq : q ∈ s) := hs q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ s, q) := Nat.Coprime.prod_right fun q h =>
      (Nat.coprime_primes hp (hq q h)).2 fun e => hps (e ▸ h)
    rw [Finset.prod_insert hps, mul_pow]
    exact (hc.pow 2 2).mul_dvd_of_dvd_of_dvd (hd p (Finset.mem_insert_self ..))
      (ih hq fun q h => hd q (Finset.mem_insert_of_mem h))

/-- Squarefree product version of the two-block criterion. -/
theorem squarefree_of_two_blocks (S : Finset ℕ)
    (hs : ∀ p ∈ S, Nat.Prime p ∧ 2 < p)
    (hb : ∀ p ∈ S, p^2 ∣ block 0 (p/2) ∧ p^2 ∣ block p (p/2)) :
    (∏ p ∈ S, p)^2 ∣ block 0 (((∏ p ∈ S, p)-1)/2) := by
  apply product_dvd (fun p h => (hs p h).1)
  intro p hp
  have ho : Odd (∏ q ∈ S.erase p, q) := by
    apply Finset.prod_induction _ _ (fun _ _ => Odd.mul) odd_one
    intro q hq
    obtain ⟨hq',hq2⟩ := hs q (Finset.mem_of_mem_erase hq)
    exact hq'.odd_of_ne_two (by omega)
  rw [← Finset.prod_erase_mul _ _ hp]
  exact odd_multiple_of_two_blocks (hs p hp).1 (hs p hp).2 ho (hb p hp).1 (hb p hp).2

/-- Multiply before dividing in the exact central binomial recurrence. The two
entries are the current term and the sum of cubes through that term. -/
private def centralPrefix : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | r+1 =>
    let prev := centralPrefix r
    let c := 2*(2*r+1)*prev.1 / (r+1)
    (c, prev.2 + c^3)

private theorem prefix_spec (r : ℕ) :
    centralPrefix r = (r.centralBinom, block 0 r) := by
  induction r with
  | zero => simp [centralPrefix, block, Nat.centralBinom]
  | succ r ih =>
    simp only [centralPrefix, ih, ← Nat.succ_mul_centralBinom_succ]
    simp [block, Finset.sum_range_succ]

private theorem prefix_interval {p : ℕ} (hp : 0 < p) (r : ℕ) :
    (centralPrefix (p+r)).2 - (centralPrefix (p-1)).2 = block p r := by
  simp only [prefix_spec, block, zero_add, Nat.sub_add_cancel hp]
  rw [Nat.add_assoc, Finset.sum_range_add]
  omega

private def checkPrime (p : ℕ) : Bool :=
  decide (p^2 ∣ (centralPrefix (p/2)).2 ∧
    p^2 ∣ (centralPrefix (p+p/2)).2 - (centralPrefix (p-1)).2)

private theorem checkPrime_spec {p : ℕ} (hp : 0 < p) (hc : checkPrime p = true) :
    p^2 ∣ block 0 (p/2) ∧ p^2 ∣ block p (p/2) := by
  unfold checkPrime at hc
  rw [decide_eq_true_eq, prefix_interval hp, prefix_spec] at hc
  exact hc

/-- The two required congruences for each eligible prime below 300. -/
private theorem check_small (i : Fin 300) :
    i.val.Prime → i.val % 7 ∈ ([3,5,6] : List ℕ) → checkPrime i.val = true := by
  revert i
  decide +kernel

/-- Bala's divisibility for every subset of the eligible primes below 300.
The product itself is unrestricted by the cutoff. -/
theorem squarefree_small (S : Finset ℕ)
    (hs : ∀ p ∈ S, p.Prime ∧ (p%7=3 ∨ p%7=5 ∨ p%7=6))
    (hlt : ∀ p ∈ S, p < 300) :
    (∏ p ∈ S, p)^2 ∣ block 0 (((∏ p ∈ S, p)-1)/2) := by
  apply squarefree_of_two_blocks
  · intro p hp
    obtain ⟨hprime,hres⟩ := hs p hp
    exact ⟨hprime, by have := hprime.two_le; rcases hres with h|h|h <;> omega⟩
  · intro p hp
    obtain ⟨hprime,hres⟩ := hs p hp
    apply checkPrime_spec hprime.pos
    apply check_small ⟨p,hlt p hp⟩ hprime
    simpa using hres

end Bala79727
