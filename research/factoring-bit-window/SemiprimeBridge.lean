import DivisorSumBitReduction
import DoublingWindow
import LocalBitCertificates

namespace SemiprimeBridge
open AbundancePrecision ArithmeticFunction DoublingWindow

/-- The selected consecutive oracle answers as an unsigned binary word. -/
def observed (n start : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => 2*observed n start h + (middleBit (query n (start+h))).val

private theorem shift_by_n {n r : ℕ} (hn : 0<n) (hr : 0<r) (j : ℕ) :
    DoublingWindow.leftFloor n (n+r) (j+1)%2=DoublingWindow.leftFloor n r (j+1)%2 := by
  have pos : 0 < 2^(j+1)*r := Nat.mul_pos (Nat.two_pow_pos _) hr
  have e : 2^(j+1)*(n+r)-1=(2^(j+1)*r-1)+n*2^(j+1) := by
    rw [Nat.mul_add, Nat.mul_comm _ n]
    omega
  unfold DoublingWindow.leftFloor
  rw [e,Nat.add_mul_div_left _ _ hn, pow_succ]
  omega

theorem observed_eq_word {n m : ℕ} (hn : 0<n) (ho : Odd n)
    (hs : sigma 1 n=n+(1+2*m)) (start h : ℕ) :
    observed n start h = word n (1+2*m) (3*n.size+start) h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    have qr := query_bit hn ho (start+h)
    change (middleBit (query n (start+h))).val =
      DoublingWindow.leftFloor n (sigma 1 n) (3*n.size+(start+h)+1)%2 at qr
    rw [hs,shift_by_n hn (by omega)] at qr
    rw [observed,word,ih,qr]
    rw [Nat.add_assoc (3*n.size) start h]

theorem semiprime_sigma {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hlt : p<q) (mid : 2*m=p+q) : sigma 1 (p*q)=p*q+(1+2*m) := by
  have prime_value {s : ℕ} (hs : s.Prime) : sigma 1 s=1+s := by
    simpa [Finset.sum_range_succ] using (sigma_one_apply_prime_pow (i:=1) hs)
  rw [isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hlt.ne),
    prime_value hp,prime_value hq,mid]
  ring

theorem midpoint_range {p q m : ℕ} (hle : p≤q) (hbal : q≤2*p)
    (mid : 2*m=p+q) : LocalBitCertificates.BalancedRange (p*q) m := by
  have h₁ : (p:ℤ)≤q := by exact_mod_cast hle
  have h₂ : (q:ℤ)≤2*p := by exact_mod_cast hbal
  have he : 2*(m:ℤ)=p+q := by exact_mod_cast mid
  have sq := congrArg (fun z:ℤ => z^2) he
  have ordered : 0 ≤ 2*(q:ℤ)-p := by linarith
  constructor
  · exact_mod_cast (show (p:ℤ)*q ≤ (m:ℤ)^2 by nlinarith [sq_nonneg ((q:ℤ)-p)])
  · exact_mod_cast (show 8*(m:ℤ)^2 ≤ 9*((p:ℤ)*q) by
      nlinarith [mul_nonneg ordered (sub_nonneg.mpr h₂)])

/-- The number of requested bits fits in half the binary input length, rounded up. -/
theorem half_bit_count {n lo W : ℕ} (hn : 0<n) (lower : n≤lo^2)
    (upper : 8*(lo+W)^2≤9*n) : (3*W).size ≤ (n.size+1)/2 := by
  apply Nat.size_le.mpr
  let t := (n.size+1)/2
  have hpow : n < (2^t)^2 := calc
    _ < 2^n.size := Nat.lt_size_self _
    _ ≤ 2^(t*2) := Nat.pow_le_pow_right (by decide) (by dsimp [t]; omega)
    _ = _ := pow_mul _ _ _
  have sm : 9*W^2 ≤ n := by
    by_cases h : lo≤4*W
    · have e := Nat.mul_le_mul_right lo h
      nlinarith
    · have e := Nat.pow_le_pow_left (show 5*W≤lo+W by omega) 2
      nlinarith
  change 3*W < 2^t
  by_contra! bad
  have e := Nat.pow_le_pow_left bad 2
  nlinarith

def splitAt (n m : ℕ) : ℕ × ℕ :=
  let d := (m^2-n).sqrt
  (m-d,m+d)

/-- Once the midpoint is located, an integer square root recovers both factors. -/
theorem splitAt_true {p q m : ℕ} (hle : p≤q) (mid : 2*m=p+q) :
    splitAt (p*q) m=(p,q) := by
  let d := m-p
  have e : p+d=m := by dsimp [d]; omega
  have f : m+d=q := by omega
  have sq : m^2=p*q+d^2 := by rw [← f,← e]; ring
  dsimp [splitAt]
  rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  exact Prod.ext (by omega) f

/-- One block of actual middle bits of the divisor-sum ratio uniquely selects
the true midpoint from an integer interval of width W. -/
theorem actual_block_unique {p q m lo W h : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hop : Odd p) (hoq : Odd q) (hlt : p<q)
    (mid : 2*m=p+q) (within : lo≤m ∧ m≤lo+W) (width : W<p*q) (cells : 3*W<2^h) :
    ∃ i ≤ (W*((p*q-1)/2^h)).size, ∀ z, lo≤z → z≤lo+W →
      (word (p*q) (1+2*z) (3*(p*q).size+i) h = observed (p*q) i h ↔ z=m) := by
  let n := p*q
  have hn : 0<n := Nat.mul_pos hp.pos hq.pos
  have ho : Odd n := hop.mul hoq
  have hs : sigma 1 n=n+(1+2*m) := semiprime_sigma hp hq hlt mid
  obtain ⟨i,hi,sep⟩ := short_word_separates hn ho width cells (3*n.size)
  refine ⟨i,hi,?_⟩
  intro z lz uz
  rw [observed_eq_word hn ho hs]
  constructor
  · intro eq
    rcases lt_trichotomy z m with hlt' | he | hgt
    · have e := sep z (m-z) (by omega) (by omega)
      rw [show z+(m-z)=m by omega] at e
      exact (e eq).elim
    · exact he
    · have e := sep m (z-m) (by omega) (by omega)
      rw [show m+(z-m)=z by omega] at e
      exact (e eq.symm).elim
  · rintro rfl
    rfl

/-- Counting lower bound for schemes that cover every locally possible midpoint.
The transcript determines a list of at most T possible candidates. -/
theorem list_capacity {n h T : ℕ}
    (code : Fin (n.sqrt/2048) → Fin (2^h))
    (capacity : ∀ z, (Finset.univ.filter (fun x => code x=z)).card ≤ T) :
    n.sqrt/2048 ≤ 2^h*T := by
  classical
  have hc := Finset.card_le_mul_card_image_of_maps_to
    (s:=Finset.univ) (t:=Finset.univ) (f:=code)
    (fun _ _ => Finset.mem_univ _) T (fun z _ => capacity z)
  simpa [Nat.mul_comm] using hc

end SemiprimeBridge
