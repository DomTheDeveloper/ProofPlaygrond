import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Bertrand

/-!
# Deterministic integer factorization and bit complexity

`CertifiedTrialFactor.BinaryMachine.factorInteger` takes an integer and returns
its prime factors with multiplicity for every input at least two. It first
extracts powers of two and three on binary tapes, then applies deterministic
trial division to any remaining cofactor.

* `BinaryMachine.factorInteger_correct` proves primality and the product identity.
* `BinaryMachine.factorInteger_smooth` gives the exact link from completed tape
  output to the integer interface for inputs with prime divisors at most three.
  `BinaryMachine.smooth_bit_bound` proves a bound of `2 * (b + 1)^2` tape
  transitions for these `b`-bit inputs. Every transition accesses a fixed number
  of finite-alphabet cells, including all operations of division by three.
* `BinaryMachine.general_bound_fails` proves that for every fixed coefficient
  and degree, arbitrarily large products of two distinct primes require more
  dividend-bit reads in the trial branch than the corresponding polynomial.

`run` exposes the trial-division counters. They record divisor tests and
individual dividend-bit reads in restoring long division. Its comparisons,
partial-remainder arithmetic and control operations add to this cost.

Checked with Lean 4.33.1 and mathlib v4.33.1. In a matching mathlib project,
run `lake env lean CertifiedTrialFactor.lean`. To run the integer interface,
use `#eval CertifiedTrialFactor.BinaryMachine.factorInteger 221` (output `[13, 17]`).
-/

namespace CertifiedTrialFactor

/-- Binary encoding length for positive inputs, extended by zero at zero. -/
def bitLength (n : ℕ) : ℕ := if n = 0 then 0 else n.log2 + 1

private theorem length_half {n : ℕ} (hn : n ≠ 0) :
    bitLength n = bitLength (n / 2) + 1 := by
  by_cases h : 2 ≤ n
  · have half : n / 2 ≠ 0 := by omega
    simp only [bitLength, if_neg hn, if_neg half]
    rw [Nat.log2_def n, if_pos h]
  · have : n = 1 := by omega
    subst n
    decide

structure Division where
  quotient : ℕ
  remainder : ℕ
  bitReads : ℕ
  deriving Repr, DecidableEq

/-- Restoring binary long division. Each nonzero call consumes the low bit of
`n`. The recursion processes all more-significant bits first. -/
def divide (n d : ℕ) : Division :=
  if n = 0 then ⟨0, 0, 0⟩ else
    let high := divide (n / 2) d
    let r := 2 * high.remainder + n % 2
    if d ≤ r then ⟨2 * high.quotient + 1, r - d, high.bitReads + 1⟩
    else ⟨2 * high.quotient, r, high.bitReads + 1⟩
termination_by n
decreasing_by apply Nat.div_lt_self <;> omega

/-- Each call produces Euclidean quotient and remainder and consumes exactly
one dividend bit per nonzero recursive frame. -/
theorem divide_spec (n d : ℕ) (hd : 0 < d) :
    divide n d = ⟨n / d, n % d, bitLength n⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp [divide, bitLength]
    · have subrun := ih (n / 2) (Nat.div_lt_self (by omega) (by decide))
      let q := n / 2 / d
      let r := 2 * (n / 2 % d) + n % 2
      have high := Nat.mod_add_div (n / 2) d
      have remBound := Nat.mod_lt (n / 2) hd
      have lowBound := Nat.mod_lt n (by decide : 0 < 2)
      have whole : r + 2 * (d * q) = n := by dsimp [r, q]; omega
      have small : r < 2 * d := by dsimp [r]; omega
      rw [divide, if_neg hn, subrun, length_half hn]
      change (if d ≤ r then Division.mk (2 * q + 1) (r - d) _ else Division.mk (2 * q) r _) = _
      by_cases take : d ≤ r
      · have num : (r - d) + d * (2 * q + 1) = n := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm d 2 q]
          omega
        obtain ⟨quot, rem⟩ := (Nat.div_mod_unique hd).2 ⟨num, by omega⟩
        simp only [if_pos take, quot, rem]
      · have num : r + d * (2 * q) = n := by rwa [Nat.mul_left_comm d 2 q]
        obtain ⟨quot, rem⟩ := (Nat.div_mod_unique hd).2 ⟨num, by omega⟩
        simp only [if_neg take, quot, rem]

private theorem log_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : a.log2 ≤ b.log2 :=
  (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (by omega : a ≠ 0)).trans hab)

private theorem length_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    bitLength a ≤ bitLength b := by
  simpa [bitLength, show a ≠ 0 by omega, show b ≠ 0 by omega] using
    Nat.succ_le_succ (log_mono ha hab)

/-- Potential for the remaining tests. A miss advances the divisor. A hit
reduces the bit length of the current cofactor by at least one. -/
private def budget (n d : ℕ) : ℕ := (n.sqrt + 1 - d) + n.log2

private theorem after_miss {n d : ℕ} (live : d * d ≤ n) :
    budget n (d + 1) < budget n d := by
  have := Nat.le_sqrt.mpr live
  unfold budget
  omega

private theorem after_hit {n d : ℕ} (hd : 2 ≤ d) (live : d * d ≤ n) :
    budget (n / d) d < budget n d := by
  have dq := (Nat.le_div_iff_mul_le (by omega : 0 < d)).2 live
  have dh : n / d ≤ n / 2 := Nat.div_le_div_left hd (by decide)
  have logs := log_mono (by omega : 0 < n / d) dh
  have half := Nat.log2_def n
  rw [if_pos (by omega : 2 ≤ n)] at half
  have roots := Nat.sqrt_le_sqrt (Nat.div_le_self n d)
  unfold budget
  omega

structure Run where
  factors : List ℕ
  tests : ℕ
  bitReads : ℕ
  deriving Repr, DecidableEq

/-- Try successive divisors until the square of the current divisor exceeds
the cofactor. After a hit, keep the divisor to extract all its copies. -/
private def scan (n d : ℕ) : Run :=
  if _h : 2 ≤ d ∧ d * d ≤ n then
    let v := divide n d
    if v.remainder = 0 then
      let tail := scan v.quotient d
      ⟨d :: tail.factors, tail.tests + 1, v.bitReads + tail.bitReads⟩
    else
      let tail := scan n (d + 1)
      ⟨tail.factors, tail.tests + 1, v.bitReads + tail.bitReads⟩
  else ⟨if 2 ≤ n then [n] else [], 0, 0⟩
termination_by budget n d
decreasing_by
  · simpa only [divide_spec n d (by have := _h.1; omega)] using after_hit _h.1 _h.2
  · exact after_miss _h.2

/-- Factor a natural number and expose the execution counters. -/
def run (n : ℕ) : Run := scan n 2

/-- Positive primes, including multiplicities, for the integer input. -/
def factor (n : ℤ) : List ℕ := (run n.toNat).factors

private theorem scan_live {n d : ℕ} (hd : 2 ≤ d) (live : d * d ≤ n) :
    scan n d = if n % d = 0 then
      let t := scan (n / d) d
      ⟨d :: t.factors, t.tests + 1, bitLength n + t.bitReads⟩
    else
      let t := scan n (d + 1)
      ⟨t.factors, t.tests + 1, bitLength n + t.bitReads⟩ := by
  rw [scan, dif_pos ⟨hd, live⟩, divide_spec n d (by omega)]

private theorem scan_done {n d : ℕ} (hn : 2 ≤ n) (done : n < d * d) :
    scan n d = ⟨[n], 0, 0⟩ := by
  rw [scan, dif_neg (by omega), if_pos hn]

/-- Every candidate strictly below `d` has already failed on `n`. -/
private def Tried (n d : ℕ) : Prop := ∀ k, 2 ≤ k → k < d → ¬ k ∣ n

private structure Valid (n d : ℕ) (r : Run) : Prop where
  product : r.factors.prod = n
  primes : ∀ p ∈ r.factors, Nat.Prime p
  tests_le : r.tests ≤ budget n d
  reads_le : r.bitReads ≤ bitLength n * r.tests

private theorem charge_reads {a t b : ℕ} (h : a ≤ b * t) : b + a ≤ b * (t + 1) := by
  rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (b * t) b]
  exact Nat.add_le_add_left h b

private theorem scan_valid (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (tried : Tried n d) :
    Valid n d (scan n d) := by
  by_cases live : d * d ≤ n
  · rw [scan_live hd live]
    by_cases hit : n % d = 0
    · rw [if_pos hit]
      have divides := Nat.dvd_of_mod_eq_zero hit
      have dq := (Nat.le_div_iff_mul_le (by omega : 0 < d)).2 live
      have tailTried : Tried (n / d) d := fun k hk hk' hdiv =>
        tried k hk hk' (hdiv.trans (Nat.div_dvd_of_dvd divides))
      have tail := scan_valid (n / d) d (by omega) hd tailTried
      have prime := Nat.prime_def_lt'.2 ⟨hd, fun k hk hk' hdiv =>
        tried k hk hk' (hdiv.trans divides)⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [List.prod_cons, tail.product, Nat.mul_comm d] using Nat.div_mul_cancel divides
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact prime
        · exact tail.primes p hp
      · exact (Nat.succ_le_succ tail.tests_le).trans (after_hit hd live)
      · have len := length_mono (by omega : 0 < n / d) (Nat.div_le_self n d)
        have h := tail.reads_le.trans (Nat.mul_le_mul_right _ len)
        exact charge_reads h
    · rw [if_neg hit]
      have tailTried : Tried n (d + 1) := by
        intro k hk hkd hdiv
        rcases Nat.lt_or_eq_of_le (show k ≤ d by omega) with lt | rfl
        · exact tried k hk lt hdiv
        · exact hit (Nat.mod_eq_zero_of_dvd hdiv)
      have tail := scan_valid n (d + 1) hn (by omega) tailTried
      refine ⟨tail.product, tail.primes,
        (Nat.succ_le_succ tail.tests_le).trans (after_miss live), ?_⟩
      exact charge_reads tail.reads_le
  · rw [scan_done hn (by omega)]
    have prime := Nat.prime_def_le_sqrt.2 ⟨hn, fun k hk hks =>
      tried k hk (lt_of_le_of_lt hks (Nat.sqrt_lt.2 (by omega)))⟩
    exact ⟨by simp, by simpa using prime, Nat.zero_le _, Nat.zero_le _⟩
termination_by budget n d
decreasing_by all_goals first | exact after_hit hd live | exact after_miss live

private theorem run_valid {n : ℕ} (hn : 2 ≤ n) : Valid n 2 (run n) :=
  scan_valid n 2 hn (by decide) (by intro k hk hk'; omega)

/-- The executable returns primes with multiplicity whose product is the
original integer. The coercion embeds their natural-number product in ℤ. -/
theorem factor_correct (n : ℤ) (hn : 2 ≤ n) :
    (↑(factor n).prod : ℤ) = n ∧ ∀ p ∈ factor n, Nat.Prime p := by
  have h := run_valid (n := n.toNat) (by omega)
  refine ⟨?_, h.primes⟩
  simpa only [factor, h.product] using Int.toNat_of_nonneg (by omega : 0 ≤ n)

/-- At most `⌊√n⌋ − 1 + ⌊log₂ n⌋` tests. Each consumes at most the input
bit length in dividend-bit reads. -/
theorem run_cost {n : ℕ} (hn : 2 ≤ n) :
    (run n).tests ≤ (n.sqrt - 1) + n.log2 ∧
    (run n).bitReads ≤ bitLength n * (run n).tests := by
  have h := run_valid hn
  exact ⟨by simpa [budget] using h.tests_le, h.reads_le⟩

private theorem no_divisor_below {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (order : p ≤ q) (hd : 2 ≤ d) (below : d < p) : ¬ d ∣ p * q := by
  intro dvd
  have hs := Nat.minFac_prime (n := d) (by omega)
  have hs2 := hs.two_le
  have hsd := Nat.minFac_le (n := d) (by omega)
  rcases hs.dvd_mul.mp ((Nat.minFac_dvd d).trans dvd) with left | right
  · rcases hp.eq_one_or_self_of_dvd _ left with h | h <;> omega
  · rcases hq.eq_one_or_self_of_dvd _ right with h | h <;> omega

private theorem scan_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (order : p ≤ q) (short : q < p * p) (d : ℕ) (hd : 2 ≤ d) (stop : d ≤ p) :
    scan (p * q) d = ⟨[p, q], p + 1 - d, bitLength (p * q) * (p + 1 - d)⟩ := by
  have live := Nat.mul_le_mul stop (Nat.le_trans stop order)
  rw [scan_live hd live]
  by_cases eq : d = p
  · subst d
    rw [if_pos (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right p q)),
      Nat.mul_div_cancel_left q hp.pos, scan_done hq.two_le short]
    simp
  · have miss : (p * q) % d ≠ 0 := fun h =>
      no_divisor_below hp hq order hd (by omega) (Nat.dvd_of_mod_eq_zero h)
    rw [if_neg miss, scan_semiprime hp hq order short (d + 1) (by omega) (by omega)]
    have step : p + 1 - d = (p + 1 - (d + 1)) + 1 := by omega
    rw [step, Nat.mul_add, Nat.mul_one]
    simp only [Nat.add_comm (bitLength (p * q))]
termination_by p - d

/-- Exact work on two prime factors `p ≤ q < p²`, including prime squares. -/
theorem semiprime_run {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p ≤ q)
    (short : q < p * p) :
    run (p * q) = ⟨[p, q], p - 1, bitLength (p * q) * (p - 1)⟩ := by
  have count : p + 1 - 2 = p - 1 := by omega
  simpa only [run, count] using scan_semiprime hp hq order short 2 (by decide) hp.two_le

/-- For every `k ≥ 1`, a product of two distinct primes has at most `2k+4`
bits and takes at least `2^k` tests. Each test reads every bit of the input. -/
theorem hard_semiprimes (k : ℕ) (hk : 1 ≤ k) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ 2 * p ∧
      2 * k + 1 ≤ bitLength (p * q) ∧ bitLength (p * q) ≤ 2 * k + 4 ∧
      2 ^ k ≤ (run (p * q)).tests ∧ bitLength (p * q) * 2 ^ k ≤ (run (p * q)).bitReads := by
  obtain ⟨p, hp, pl, pu⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ k) (Nat.two_pow_pos k).ne'
  obtain ⟨q, hq, order, qu⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have atLeastTwo : 2 ≤ 2 ^ k := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have short := lt_of_le_of_lt qu (Nat.mul_lt_mul_of_pos_right (by omega : 2 < p) hp.pos)
  have lower : 2 ^ (2 * k) ≤ p * q := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul pl.le (Nat.le_trans pl.le order.le)
  have upper : p * q < 2 ^ (2 * k + 4) := by
    calc
      p * q ≤ (2 * 2 ^ k) * (4 * 2 ^ k) := Nat.mul_le_mul pu (by omega)
      _ = 2 ^ (2 * k + 3) := by
        rw [show 2 * k = k + k by omega, pow_add, pow_add]
        ring
      _ < 2 ^ (2 * k + 4) := by
        rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega, Nat.pow_succ 2 (2 * k + 3)]
        have := Nat.two_pow_pos (2 * k + 3)
        omega
  have pos := Nat.mul_pos hp.pos hq.pos
  have lo := (Nat.le_log2 pos.ne').2 lower
  have hi := (Nat.log2_lt pos.ne').2 upper
  have len : bitLength (p * q) = (p * q).log2 + 1 := if_neg pos.ne'
  refine ⟨p, q, hp, hq, order, qu, by omega, by omega, ?_⟩
  rw [semiprime_run hp hq order.le short]
  change 2 ^ k ≤ p - 1 ∧ bitLength (p * q) * 2 ^ k ≤ bitLength (p * q) * (p - 1)
  exact ⟨by omega, Nat.mul_le_mul_left _ (by omega)⟩

/-- A concrete choice of `k` for which the exponential exceeds the budget. -/
private theorem large_exponent (c e minimum : ℕ) :
    ∃ k, minimum ≤ k ∧ 1 ≤ k ∧ c * (2 * k + 4) ^ e < 2 ^ k := by
  let t := c + e + minimum + 3
  let k := 2 ^ (2 * t)
  have ht : c + e + minimum + 3 = t := rfl
  have tBound : 2 * t + 2 ≤ 2 ^ t := by
    dsimp [t]
    rw [Nat.pow_add 2 (c + e + minimum) 3]
    have := Nat.lt_two_pow_self (n := c + e + minimum)
    omega
  have htPow := Nat.lt_two_pow_self (n := t)
  have hk : 2 * t < k := Nat.lt_two_pow_self
  have scale : 2 * k + 4 ≤ 2 ^ (2 * t + 2) := by
    rw [Nat.pow_add 2 (2 * t) 2]
    change 2 * k + 4 ≤ k * 4
    omega
  have exponent : c + (2 * t + 2) * e ≤ k := by
    calc
      c + (2 * t + 2) * e ≤ (2 * t + 2) * (e + 1) := by
        rw [Nat.mul_add (2 * t + 2) e 1, Nat.mul_one]
        omega
      _ ≤ 2 ^ t * 2 ^ t := Nat.mul_le_mul tBound (by omega)
      _ = k := by
        change 2 ^ t * 2 ^ t = 2 ^ (2 * t)
        rw [two_mul t, Nat.pow_add 2 t t]
  refine ⟨k, by omega, by omega, ?_⟩
  calc
    c * (2 * k + 4) ^ e < 2 ^ c * (2 ^ (2 * t + 2)) ^ e :=
      Nat.mul_lt_mul_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left scale e)
        (Nat.pow_pos (Nat.two_pow_pos _))
    _ = 2 ^ (c + (2 * t + 2) * e) := by rw [Nat.pow_add 2 c, Nat.pow_mul]
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) exponent

/-- Even on products of comparable, distinct primes, no polynomial in the
input bit length bounds this algorithm's divisor tests or dividend-bit reads. -/
theorem exceeds_every_polynomial (c e minimumBits : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ 2 * p ∧ minimumBits ≤ bitLength (p * q) ∧
      c * bitLength (p * q) ^ e < (run (p * q)).tests ∧
      c * bitLength (p * q) ^ e < (run (p * q)).bitReads := by
  obtain ⟨k, big, positive, beats⟩ := large_exponent c e minimumBits
  obtain ⟨p, q, hp, hq, order, close, lo, hi, tests, reads⟩ := hard_semiprimes k positive
  have large := (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hi e)).trans_lt beats
  have one : 1 ≤ bitLength (p * q) := by omega
  have bits : 2 ^ k ≤ bitLength (p * q) * 2 ^ k := by simpa using Nat.mul_le_mul_right (2 ^ k) one
  exact ⟨p, q, hp, hq, order, close, by omega,
    large.trans_le tests, large.trans_le (bits.trans reads)⟩

example : run 221 = ⟨[13, 17], 12, 96⟩ := by
  exact semiprime_run (p := 13) (q := 17) (by decide) (by decide) (by decide) (by decide)

end CertifiedTrialFactor

/-! ## Bit machine for extracting twos and threes -/

namespace CertifiedTrialFactor.BinaryMachine

/-- A positive binary input, starting at the least significant end. The `one`
marker is its highest set bit. -/
inductive Word where
  | one
  | even (high : Word)
  | odd (high : Word)
  deriving Repr, DecidableEq

def Word.value : Word → ℕ
  | .one => 1
  | .even w => 2 * w.value
  | .odd w => 2 * w.value + 1

def Word.width : Word → ℕ
  | .one => 1
  | .even w | .odd w => w.width + 1

private theorem Word.positive (w : Word) : 0 < w.value := by
  induction w with
  | one => decide
  | even w ih => simp only [Word.value]; omega
  | odd w ih => simp only [Word.value]; omega

def Word.encode (n : ℕ) : Word :=
  if n < 2 then .one else
    let high := Word.encode (n / 2)
    if n % 2 = 0 then .even high else .odd high
termination_by n
decreasing_by apply Nat.div_lt_self <;> omega

theorem Word.encode_spec (n : ℕ) (hn : 0 < n) :
    (Word.encode n).value = n ∧ (Word.encode n).width = bitLength n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 2
    · have eq : n = 1 := by omega
      subst n
      rw [Word.encode, if_pos (by decide : 1 < 2)]
      decide
    · have half : 0 < n / 2 := by omega
      obtain ⟨value, size⟩ := ih (n / 2) (Nat.div_lt_self hn (by decide)) half
      have len : bitLength n = bitLength (n / 2) + 1 := by
        simp only [bitLength, if_neg hn.ne', if_neg half.ne']
        rw [Nat.log2_def n, if_pos (by omega : 2 ≤ n)]
      rw [Word.encode, if_neg small]
      split <;> simp only [Word.value, Word.width, value, size, len, and_true] <;> omega

inductive Rem where
  | zero | one | two
  deriving Repr, DecidableEq

private def Rem.value : Rem → ℕ | .zero => 0 | .one => 1 | .two => 2

/-- Quotient digit and next remainder for each of the six possible inputs. -/
private def cell : Rem → Bool → Bool × Rem
  | .zero, false => (false, .zero)
  | .zero, true  => (false, .one)
  | .one,  false => (false, .two)
  | .one,  true  => (true, .zero)
  | .two,  false => (true, .one)
  | .two,  true  => (true, .two)

private theorem cell_correct (r : Rem) (b : Bool) :
    3 * (cell r b).1.toNat + (cell r b).2.value = 2 * r.value + b.toNat := by
  cases r <;> cases b <;> decide

/-- A blank quotient stack holds zero. Skip high zeroes when pushing digits. -/
private def push (b : Bool) : Option Word → Option Word
  | none => if b then some .one else none
  | some w => some (if b then .odd w else .even w)

private def magnitude : Option Word → ℕ | none => 0 | some w => w.value
private def widthOf : Option Word → ℕ | none => 0 | some w => w.width

private theorem push_value (b : Bool) (w : Option Word) :
    magnitude (push b w) = 2 * magnitude w + b.toNat := by
  cases w <;> cases b <;> simp [push, magnitude, Word.value]

private theorem push_width (b : Bool) (w : Option Word) :
    widthOf (push b w) ≤ widthOf w + 1 := by
  cases w <;> cases b <;> simp [push, widthOf, Word.width]

structure PartialQuotient where
  quotient : Option Word
  remainder : Rem
  deriving Repr, DecidableEq

/-- Recover the original value from a quotient and remainder modulo three. -/
def PartialQuotient.total (q : PartialQuotient) : ℕ :=
  3 * magnitude q.quotient + q.remainder.value

private def appendDigit (q : PartialQuotient) (b : Bool) : PartialQuotient :=
  let (outBit, rem) := cell q.remainder b
  ⟨push outBit q.quotient, rem⟩

private theorem append_total (q : PartialQuotient) (b : Bool) :
    (appendDigit q b).total = 2 * q.total + b.toNat := by
  have h := cell_correct q.remainder b
  simp only [appendDigit, PartialQuotient.total, push_value]
  omega

/-- Mathematical specification of the two tape sweeps below. -/
private def divThree : Word → PartialQuotient
  | .one => ⟨none, .one⟩
  | .even w => appendDigit (divThree w) false
  | .odd w => appendDigit (divThree w) true

private theorem divThree_spec (w : Word) :
    (divThree w).total = w.value ∧ widthOf (divThree w).quotient < w.width := by
  induction w with
  | one => decide
  | even w ih =>
    refine ⟨by rw [divThree, append_total, ih.1]; rfl, ?_⟩
    exact (push_width _ _).trans_lt (Nat.succ_lt_succ ih.2)
  | odd w ih =>
    refine ⟨by rw [divThree, append_total, ih.1]; rfl, ?_⟩
    exact (push_width _ _).trans_lt (Nat.succ_lt_succ ih.2)

/-- Each output cell carries one bit. With an implicit leading 1, `false`
encodes the binary prime 10 and `true` encodes the binary prime 11. -/
def primeDigit (b : Bool) : ℕ := if b then 3 else 2

inductive Stop where
  | complete (output : List Bool)
  | residual (partialQuotient : PartialQuotient) (output : List Bool)
  deriving Repr, DecidableEq

/-- Finite control with four stacks of fixed-alphabet cells for the input,
reversed digits, quotient, and output. The stack roles change after a division.
All accesses in `step` are to stack tops. -/
inductive State where
  | inspect (input : Word) (output : List Bool)
  | reverseInput (input : Word) (pending : List Bool) (output : List Bool)
  | divide (pending : List Bool) (q : PartialQuotient) (output : List Bool)
  | halt (result : Stop)
  deriving Repr, DecidableEq

/-- One deterministic machine transition. All branch tests use at most a
fixed number of symbols. The six-entry table implements the arithmetic. -/
def step : State → State
  | .inspect .one out => .halt (.complete out)
  | .inspect (.even high) out => .inspect high (false :: out)
  | .inspect (.odd high) out => .reverseInput (.odd high) [] out
  | .reverseInput .one bits out => .divide bits ⟨none, .one⟩ out
  | .reverseInput (.even high) bits out => .reverseInput high (false :: bits) out
  | .reverseInput (.odd high) bits out => .reverseInput high (true :: bits) out
  | .divide (b :: bs) q out => .divide bs (appendDigit q b) out
  | .divide [] ⟨some w, .zero⟩ out => .inspect w (true :: out)
  | .divide [] q out => .halt (.residual q out)
  | .halt result => .halt result

/-- The natural number is a mathematical clock external to the bit machine. -/
def advance : ℕ → State → State
  | 0, s => s
  | _ + 1, .halt result => .halt result
  | t + 1, s => advance t (step s)

private theorem halt_stable (t : ℕ) (s : Stop) : advance t (.halt s) = .halt s := by
  cases t <;> rfl

private theorem advance_add (m n : ℕ) (s : State) :
    advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih =>
    rw [Nat.succ_add]
    cases s with
    | halt r => simp [halt_stable]
    | _ => exact ih _

private def sweepLength : Word → ℕ
  | .one => 1
  | .even w | .odd w => sweepLength w + 2

private theorem sweep_bound (w : Word) : sweepLength w ≤ 2 * w.width := by
  induction w <;> simp_all [sweepLength, Word.width] <;> omega

private theorem sweeps (w : Word) (pending out : List Bool) :
    advance (sweepLength w) (.reverseInput w pending out) = .divide pending (divThree w) out := by
  induction w generalizing pending with
  | one => rfl
  | even w ih =>
    change advance (sweepLength w + 1) (.reverseInput w (false :: pending) out) = _
    rw [advance_add, ih]; rfl
  | odd w ih =>
    change advance (sweepLength w + 1) (.reverseInput w (true :: pending) out) = _
    rw [advance_add, ih]; rfl

private def product (out : List Bool) : ℕ := (out.map primeDigit).prod
private def Stop.output : Stop → List Bool | .complete out | .residual _ out => out
private def Stop.cofactor : Stop → ℕ | .complete _ => 1 | .residual q _ => q.total
private def Stop.clean : Stop → Prop
  | .complete _ => True
  | .residual q _ => 2 ≤ q.total ∧ q.total % 2 = 1 ∧ q.total % 3 ≠ 0

private def limit (b : ℕ) : ℕ := (2 * b + 2) * (b + 1)

private theorem shorter {a b : ℕ} (lt : a < b) : limit a + (2 * b + 2) ≤ limit b := by
  have bound := Nat.mul_le_mul (by omega : 2 * a + 2 ≤ 2 * b + 2) (by omega : a + 1 ≤ b)
  exact (Nat.add_le_add_right bound _).trans_eq (Nat.mul_succ _ _).symm

/-- The finite control either finishes or leaves an odd cofactor greater than
one with nonzero remainder modulo three. The equation tracks every emitted
prime and the time bound includes both sweeps of every attempted division. -/
private theorem finishes (w : Word) (out : List Bool) :
    ∃ t ≤ limit w.width, ∃ s : Stop, advance t (.inspect w out) = .halt s ∧
      s.cofactor * product s.output = w.value * product out ∧ s.clean := by
  cases w with
  | one => exact ⟨1, by decide, .complete out, rfl, rfl, trivial⟩
  | even high =>
    obtain ⟨t, ht, s, reached, inv, clean⟩ := finishes high (false :: out)
    have timing := shorter (a := high.width) (b := (Word.even high).width) (Nat.lt_succ_self _)
    refine ⟨t + 1, by omega, s, reached, inv.trans ?_, clean⟩
    simp [product, primeDigit, Word.value, Nat.mul_assoc, Nat.mul_comm]
  | odd high =>
    let w := Word.odd high
    have sweep := sweeps w [] out
    have price := sweep_bound w
    obtain ⟨quot, rem, eqD⟩ : ∃ q r, divThree w = ⟨q, r⟩ := by
      cases d : divThree w with | mk q r => exact ⟨q, r, rfl⟩
    have arrive : advance (sweepLength w + 1) (.inspect w out) = .divide [] ⟨quot, rem⟩ out := by
      change advance (sweepLength w) (.reverseInput w [] out) = _
      rwa [eqD] at sweep
    have spec := divThree_spec w
    rw [eqD] at spec
    obtain ⟨val, narrower⟩ := spec
    by_cases exactDiv : rem = .zero
    · subst rem
      cases quot with
      | none =>
        have pos := w.positive
        change 0 = w.value at val
        omega
      | some q =>
        change q.width < w.width at narrower
        obtain ⟨t, ht, s, reached, inv, clean⟩ := finishes q (true :: out)
        have timing := shorter narrower
        refine ⟨(sweepLength w + 1) + (t + 1), by change _ ≤ limit w.width; omega, s, ?_, ?_, clean⟩
        · rw [advance_add, arrive]; exact reached
        · change 3 * q.value + 0 = w.value at val
          change _ = w.value * product out
          rw [inv, ← val]
          simp [product, primeDigit, Nat.mul_assoc, Nat.mul_comm]
    · have finish : step (.divide [] ⟨quot, rem⟩ out) = .halt (.residual ⟨quot, rem⟩ out) := by
        cases rem <;> cases quot <;> simp_all [step]
      have room : 2 * w.width + 2 ≤ limit w.width := by
        simp [limit]
      refine ⟨(sweepLength w + 1) + 1, by change _ ≤ limit w.width; omega,
        .residual ⟨quot, rem⟩ out, ?_, ?_, ?_⟩
      · rw [advance_add, arrive]; exact finish
      · exact congrArg (fun x => x * product out) val
      · have pos := high.positive
        have remCases : rem.value = 1 ∨ rem.value = 2 := by cases rem <;> simp_all [Rem.value]
        change 3 * magnitude quot + rem.value = 2 * high.value + 1 at val
        change 2 ≤ 3 * magnitude quot + rem.value ∧ (3 * magnitude quot + rem.value) % 2 = 1 ∧
          (3 * magnitude quot + rem.value) % 3 ≠ 0
        omega
termination_by w.width
decreasing_by all_goals first | exact Nat.lt_succ_self _ | exact narrower

/-- All prime divisors are at most three. This includes every `2 ^ a * 3 ^ b`. -/
def ThreeSmooth (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 3

private theorem output_prime (out : List Bool) : ∀ p ∈ out.map primeDigit, p.Prime := by
  intro p hp
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
  cases b <;> decide

/-- A single fixed binary machine finishes within `2 * (b + 1)²` transitions
on every three-smooth `b`-bit input. Its completed output already encodes all
the primes, using one fixed-alphabet cell per factor. -/
theorem smooth_bit_bound (n : ℕ) (hn : 0 < n) (smooth : ThreeSmooth n) :
    ∃ t ≤ 2 * (bitLength n + 1) ^ 2, ∃ out : List Bool,
      advance t (.inspect (Word.encode n) []) = .halt (.complete out) ∧
      (out.map primeDigit).prod = n ∧ ∀ p ∈ out.map primeDigit, p.Prime := by
  obtain ⟨value, width⟩ := Word.encode_spec n hn
  obtain ⟨t, ht, s, reached, inv, clean⟩ := finishes (Word.encode n) []
  have budget : limit (Word.encode n).width = 2 * (bitLength n + 1) ^ 2 := by
    rw [width]; unfold limit; ring
  have total : s.cofactor * product s.output = n := by simpa [product, value] using inv
  cases s with
  | complete out =>
    refine ⟨t, ht.trans_eq budget, out, reached, ?_, output_prime out⟩
    simpa [Stop.cofactor, Stop.output, product] using total
  | residual q out =>
    obtain ⟨two, odd, three⟩ := clean
    change q.total * product out = n at total
    have dvd : q.total ∣ n := ⟨product out, total.symm⟩
    have hp := Nat.minFac_prime (n := q.total) (by omega)
    have restriction := smooth _ hp ((Nat.minFac_dvd q.total).trans dvd)
    have floor := hp.two_le
    have exactDiv := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd q.total)
    rcases (by omega : q.total.minFac = 2 ∨ q.total.minFac = 3) with eq | eq <;> rw [eq] at exactDiv <;> omega

/-- This is the polynomial input family with explicit exponents. -/
theorem smooth_two_three (a b : ℕ) : ThreeSmooth (2 ^ a * 3 ^ b) := by
  intro p hp dvd
  rcases hp.dvd_mul.mp dvd with two | three
  · have divides := hp.dvd_of_dvd_pow two
    exact (Nat.le_of_dvd (by decide : 0 < 2) divides).trans (by decide)
  · exact Nat.le_of_dvd (by decide : 0 < 3) (hp.dvd_of_dvd_pow three)

/-- Execute the bit machine for a sufficient number of transitions. Its halt
states are absorbing. The general factorer handles any remaining cofactor. -/
def factorWord (w : Word) : List ℕ :=
  match advance (limit w.width) (.inspect w []) with
  | .halt (.complete out) => out.map primeDigit
  | .halt (.residual q out) => out.map primeDigit ++ CertifiedTrialFactor.factor (q.total : ℤ)
  | _ => CertifiedTrialFactor.factor (w.value : ℤ)

private theorem run_to_limit {w : Word} {t : ℕ} {s : Stop} (ht : t ≤ limit w.width)
    (reached : advance t (.inspect w []) = .halt s) :
    advance (limit w.width) (.inspect w []) = .halt s := by
  have clock : limit w.width = t + (limit w.width - t) := by omega
  rw [clock, advance_add, reached, halt_stable]

/-- All positive binary inputs have a complete prime factorization, including
inputs for which the finite control hands a cofactor to trial division. -/
theorem factorWord_correct (w : Word) :
    (factorWord w).prod = w.value ∧ ∀ p ∈ factorWord w, p.Prime := by
  obtain ⟨t, ht, s, reached, inv, clean⟩ := finishes w []
  rw [factorWord, run_to_limit ht reached]
  cases s with
  | complete out =>
    exact ⟨by simpa [Stop.cofactor, Stop.output, product] using inv, output_prime out⟩
  | residual q out =>
    obtain ⟨two, _, _⟩ := clean
    obtain ⟨eq, prime⟩ := CertifiedTrialFactor.factor_correct (q.total : ℤ) (by exact_mod_cast two)
    have tail : (CertifiedTrialFactor.factor (q.total : ℤ)).prod = q.total := by exact_mod_cast eq
    constructor
    · rw [List.prod_append, tail]
      simpa [Stop.cofactor, Stop.output, product, Nat.mul_comm] using inv
    · intro p hp
      exact (List.mem_append.mp hp).elim (output_prime out p) (prime p)

/-- On an odd input greater than one with nonzero remainder modulo three, the
prepass hands the entire original integer to the general trial factorer. -/
theorem full_residual (w : Word) (big : 1 < w.value) (odd : w.value % 2 = 1)
    (three : w.value % 3 ≠ 0) :
    ∃ t ≤ 2 * w.width + 2, ∃ q : PartialQuotient,
      advance t (.inspect w []) = .halt (.residual q []) ∧
      q.total = w.value := by
  cases w with
  | one => contradiction
  | even w => change (2 * w.value) % 2 = 1 at odd; omega
  | odd high =>
    let w := Word.odd high
    let q := divThree w
    have eq : q.total = w.value := (divThree_spec w).1
    have nonzero : q.remainder ≠ .zero := by
      intro h
      have zero : q.remainder.value = 0 := by rw [h]; rfl
      change 3 * magnitude q.quotient + q.remainder.value = w.value at eq
      change w.value % 3 ≠ 0 at three
      omega
    have finish : step (.divide [] q []) = .halt (.residual q []) := by
      generalize q = v at nonzero ⊢
      rcases v with ⟨a, r⟩
      cases r <;> cases a <;> simp_all [step]
    have start : advance (sweepLength w + 1) (.inspect w []) = .divide [] q [] := sweeps w [] []
    have bound := sweep_bound w
    refine ⟨(sweepLength w + 1) + 1, by change _ ≤ 2 * w.width + 2; omega, q, ?_, eq⟩
    rw [advance_add, start]
    exact finish

/-- Integer entry point for the finite-control prepass followed by trial division. -/
def factorInteger (n : ℤ) : List ℕ :=
  if n < 2 then [] else factorWord (Word.encode n.toNat)

theorem factorInteger_correct (n : ℤ) (hn : 2 ≤ n) :
    (↑(factorInteger n).prod : ℤ) = n ∧ ∀ p ∈ factorInteger n, p.Prime := by
  have value := (Word.encode_spec n.toNat (by omega)).1
  rw [factorInteger, if_neg (by omega)]
  obtain ⟨eq, primes⟩ := factorWord_correct (Word.encode n.toNat)
  rw [eq, value, Int.toNat_of_nonneg (by omega)]
  exact ⟨rfl, primes⟩

/-- The bounded binary computation gives exactly the output of the general
integer entry point, so the trial-division branch is bypassed on this family. -/
theorem factorInteger_smooth (n : ℤ) (hn : 2 ≤ n) (smooth : ThreeSmooth n.toNat) :
    ∃ t ≤ 2 * (bitLength n.toNat + 1) ^ 2, ∃ out : List Bool,
      advance t (.inspect (Word.encode n.toNat) []) = .halt (.complete out) ∧
      factorInteger n = out.map primeDigit := by
  obtain ⟨t, time, out, reached, _, _⟩ := smooth_bit_bound n.toNat (by omega) smooth
  have width := (Word.encode_spec n.toNat (by omega)).2
  have bound : limit (Word.encode n.toNat).width = 2 * (bitLength n.toNat + 1) ^ 2 := by
    rw [width]; unfold limit; ring
  refine ⟨t, time, out, reached, ?_⟩
  rw [factorInteger, if_neg (by omega), factorWord, run_to_limit (time.trans_eq bound.symm) reached]

/-- Comparable distinct primes give arbitrarily large inputs on which the
binary prepass leaves the whole number for the trial-division branch and that
branch alone reads more dividend bits than the proposed polynomial bound. -/
theorem general_bound_fails (c e minimumBits : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ 2 * p ∧ minimumBits ≤ bitLength (p * q) ∧
      ∃ t ≤ 2 * bitLength (p * q) + 2, ∃ residual : PartialQuotient,
        advance t (.inspect (Word.encode (p * q)) []) = .halt (.residual residual []) ∧
        residual.total = p * q ∧ c * bitLength (p * q) ^ e < (run residual.total).bitReads := by
  obtain ⟨p, q, hp, hq, order, close, big, _, cost⟩ :=
    exceeds_every_polynomial c e (minimumBits + 6)
  have pos := Nat.mul_pos hp.pos hq.pos
  have pBig : 3 < p := by
    by_contra! small
    have le := Nat.mul_le_mul small (by omega : q ≤ 6)
    have log := (Nat.log2_lt pos.ne').2 (by omega : p * q < 2 ^ 5)
    simp only [bitLength, if_neg pos.ne'] at big
    omega
  have avoid (d : ℕ) (prime : d.Prime) (lo : d < p) : ¬ d ∣ p * q := by
    intro dvd
    have hd := prime.two_le
    rcases prime.dvd_mul.mp dvd with left | right
    · rcases hp.eq_one_or_self_of_dvd d left with h | h <;> omega
    · rcases hq.eq_one_or_self_of_dvd d right with h | h <;> omega
  have noTwo := avoid 2 Nat.prime_two (by omega)
  have noThree := avoid 3 Nat.prime_three pBig
  rw [Nat.dvd_iff_mod_eq_zero] at noTwo noThree
  obtain ⟨value, width⟩ := Word.encode_spec (p * q) pos
  have more : 1 < p * q := by
    have le := Nat.mul_le_mul hp.two_le hq.two_le
    omega
  obtain ⟨t, bound, residual, halt, eq⟩ := full_residual (Word.encode (p * q))
    (by omega) (by omega) (by omega)
  rw [value] at eq
  exact ⟨p, q, hp, hq, order, close, by omega, t, by simpa only [width] using bound,
    residual, halt, eq, by simpa only [eq] using cost⟩

end CertifiedTrialFactor.BinaryMachine

#print axioms CertifiedTrialFactor.divide_spec
#print axioms CertifiedTrialFactor.factor_correct
#print axioms CertifiedTrialFactor.run_cost
#print axioms CertifiedTrialFactor.semiprime_run
#print axioms CertifiedTrialFactor.exceeds_every_polynomial
#print axioms CertifiedTrialFactor.BinaryMachine.factorInteger_correct
#print axioms CertifiedTrialFactor.BinaryMachine.smooth_bit_bound
#print axioms CertifiedTrialFactor.BinaryMachine.factorInteger_smooth
#print axioms CertifiedTrialFactor.BinaryMachine.general_bound_fails
