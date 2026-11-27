import Std

/-!
# Prime factorization from bounded-divisor queries

Checked with Lean 4.19.0. Run `lean FactorizationThreshold.lean` in a directory
containing this file. Only the standard library is needed.

For positive n, a correct bounded-divisor oracle gives a prime factorization
using at most 2 * floor(log₂ n) Boolean queries, counting all multiplicities.
A query asks whether n has a divisor in [2,k], including n itself if k ≥ n.
The direct implementation computes k! modulo n. On semiprimes n = p*q with
p ≤ q ≤ 2*p, its first successful bracketing query requires at least p modular
multiplications. On prime squares that one query exceeds every fixed polynomial
in the binary input length on arbitrarily large inputs.

The search-to-decision reduction and the factorial gcd test are classical ideas.
`factor_correct` proves the query bound and validates the full prime factor list.
`full_run_exceeds_every_polynomial` proves the lower bound for the complete
execution with the cost of every sequential factorial evaluation included.

The Maryland lecture notes describe the threshold reduction.
https://www.cs.umd.edu/class/fall2024/cmsc657/Lecture-10.pdf

Harvey describes faster ways to evaluate products for factoring.
https://web.maths.unsw.edu.au/~davidharvey/talks/factoring2.pdf
-/

namespace FactorizationThreshold

def HasDivisor (n k : Nat) : Prop :=
  ∃ d, 2 ≤ d ∧ d ≤ k ∧ d ∣ n

def CorrectOracle (ask : Nat → Nat → Bool) : Prop :=
  ∀ n k, 2 ≤ n → (ask n k = true ↔ HasDivisor n k)

/-- A positive integer with precisely the usual primality condition on its divisors. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, 2 ≤ d → d ∣ p → d = p

structure LeastDivisor (n p : Nat) : Prop where
  ge_two : 2 ≤ p
  divides : p ∣ n
  least : ∀ d, 2 ≤ d → d ∣ n → p ≤ d

theorem leastDivisor_exists {n : Nat} (hn : 2 ≤ n) : ∃ p, LeastDivisor n p := by
  have descend (d : Nat) : 2 ≤ d → d ∣ n → ∃ p, LeastDivisor n p := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro hd hdvd
      by_cases h : ∃ e, 2 ≤ e ∧ e ∣ n ∧ e < d
      · obtain ⟨e, he, hevd, hed⟩ := h
        exact ih e hed he hevd
      · refine ⟨d, hd, hdvd, ?_⟩
        intro e he hevd
        apply Nat.le_of_not_gt
        intro hed
        exact h ⟨e, he, hevd, hed⟩
  exact descend n hn (Nat.dvd_refl n)

theorem LeastDivisor.prime {n p : Nat} (hp : LeastDivisor n p) : IsPrime p := by
  refine ⟨hp.ge_two, ?_⟩
  intro d hd hdvd
  exact Nat.le_antisymm (Nat.le_of_dvd (by have := hp.ge_two; omega) hdvd)
    (hp.least d hd (Nat.dvd_trans hdvd hp.divides))

theorem LeastDivisor.threshold {n p : Nat} (hp : LeastDivisor n p) (k : Nat) :
    HasDivisor n k ↔ p ≤ k := by
  constructor
  · rintro ⟨d, hd, hdk, hdvd⟩
    exact Nat.le_trans (hp.least d hd hdvd) hdk
  · intro hpk
    exact ⟨p, hp.ge_two, hpk, hp.divides⟩

structure Run (α : Type) where
  value : α
  cost : Nat
  deriving Repr, DecidableEq

/-- Unit cost counts queries. Using the identity function counts the modular
multiplications performed by the direct factorial oracle at each threshold. -/
@[simp] def unitCost (_ : Nat) : Nat := 1

/-- Charge the chosen cost and execute only the selected continuation. -/
def query {α : Type} (cost : Nat) (answer : Bool) (yes no : Unit → Run α) : Run α :=
  let r := if answer then yes () else no ()
  ⟨r.value, r.cost + cost⟩

/-- Search the interval [lo, lo + 2^depth). Its first true value is the target. -/
def bisect (queryCost : Nat → Nat) (ask : Nat → Bool) (lo : Nat) : Nat → Run Nat
  | 0 => ⟨lo, 0⟩
  | depth + 1 =>
    let half := 2 ^ depth
    query (queryCost (lo + half - 1)) (ask (lo + half - 1))
      (fun _ => bisect queryCost ask lo depth)
      (fun _ => bisect queryCost ask (lo + half) depth)

/-- Test upper endpoints 2^(level+1)-1 until one contains the target. -/
def bracket (queryCost : Nat → Nat) (ask : Nat → Bool) (level : Nat) : Nat → Run Nat
  | 0 => ⟨0, 0⟩
  | fuel + 1 =>
    query (queryCost (2 ^ (level + 1) - 1)) (ask (2 ^ (level + 1) - 1))
      (fun _ => bisect queryCost ask (2 ^ level) level)
      (fun _ => bracket queryCost ask (level + 1) fuel)

def firstFactor (queryCost : Nat → Nat) (ask : Nat → Nat → Bool) (n : Nat) : Run Nat :=
  bracket queryCost (ask n) 1 n.log2

private theorem noAnswer {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

private theorem bisect_correct {ask : Nat → Bool} {p : Nat}
    (spec : ∀ k, ask k = true ↔ p ≤ k) (depth lo : Nat)
    (lower : lo ≤ p) (upper : p < lo + 2 ^ depth) :
    bisect unitCost ask lo depth = ⟨p, depth⟩ := by
  induction depth generalizing lo with
  | zero =>
    simp only [Nat.pow_zero] at upper
    have e : lo = p := by omega
    simp [bisect, e]
  | succ d ih =>
    rw [Nat.pow_succ] at upper
    have hpos := Nat.two_pow_pos d
    by_cases left : p < lo + 2 ^ d
    · have yes := (spec (lo + 2 ^ d - 1)).2 (by omega)
      simp [bisect, query, yes, ih lo lower left]
    · have no := noAnswer (fun h => left (by have := (spec _).1 h; omega))
        (b := ask (lo + 2 ^ d - 1))
      have a : lo + 2 ^ d ≤ p := by omega
      have b : p < lo + 2 ^ d + 2 ^ d := by omega
      simp [bisect, query, no, ih _ a b]

private theorem bracket_correct {ask : Nat → Bool} {p j : Nat}
    (spec : ∀ k, ask k = true ↔ p ≤ k)
    (pLower : 2 ^ j ≤ p) (pUpper : p < 2 ^ (j + 1))
    (fuel level : Nat) (hLevel : level ≤ j) (hFuel : j < level + fuel) :
    bracket unitCost ask level fuel = ⟨p, (j + 1 - level) + j⟩ := by
  induction fuel generalizing level with
  | zero => omega
  | succ f ih =>
    by_cases same : level = j
    · subst level
      have yes := (spec (2 ^ (j + 1) - 1)).2 (by omega)
      have upper : p < 2 ^ j + 2 ^ j := by
        rw [Nat.pow_succ] at pUpper
        omega
      simp [bracket, query, yes, bisect_correct spec j _ pLower upper]
    · have levels : level + 1 ≤ j := by omega
      have monotone := Nat.pow_le_pow_right (by decide : 0 < 2) levels
      have hpos := Nat.two_pow_pos (level + 1)
      have no : ask (2 ^ (level + 1) - 1) = false := by
        apply noAnswer
        intro h
        have := (spec _).1 h
        omega
      have recResult := ih (level + 1) levels (by omega)
      simp [bracket, query, no, recResult]
      omega

private theorem power_log_lower {n : Nat} (hn : 0 < n) : 2 ^ n.log2 ≤ n :=
  (Nat.le_log2 (by omega)).1 (Nat.le_refl _)

private theorem log_positive {n : Nat} (hn : 2 ≤ n) : 1 ≤ n.log2 :=
  (Nat.le_log2 (by omega)).2 (by simpa using hn)

private theorem log_monotone {a b : Nat} (ha : 0 < a) (hab : a ≤ b) :
    a.log2 ≤ b.log2 :=
  (Nat.le_log2 (by omega)).2 (Nat.le_trans (power_log_lower ha) hab)

theorem firstFactor_correct {ask : Nat → Nat → Bool} (spec : CorrectOracle ask)
    {n p : Nat} (hn : 2 ≤ n) (hp : LeastDivisor n p) :
    firstFactor unitCost ask n = ⟨p, 2 * p.log2⟩ := by
  have pp : 0 < p := by have := hp.ge_two; omega
  have pn := Nat.le_of_dvd (by omega : 0 < n) hp.divides
  have pl := log_positive hp.ge_two
  have pln := log_monotone pp pn
  have lower := power_log_lower pp
  have upper : p < 2 ^ (p.log2 + 1) := (Nat.log2_lt (by omega)).1 (by omega)
  have r := bracket_correct (fun k => (spec n k hn).trans (hp.threshold k))
    lower upper n.log2 1 pl (by omega)
  simpa [firstFactor, Nat.two_mul] using r

def product : List Nat → Nat
  | [] => 1
  | p :: ps => p * product ps

/-- Fuel bounds the number of extracted factors. Correct inputs use n.log2. -/
def factorAux (queryCost : Nat → Nat) (ask : Nat → Nat → Bool) : Nat → Nat → Run (List Nat)
  | 0, _ => ⟨[], 0⟩
  | fuel + 1, n =>
    if n < 2 then ⟨[], 0⟩ else
      let r := firstFactor queryCost ask n
      let tail := factorAux queryCost ask fuel (n / r.value)
      ⟨r.value :: tail.value, r.cost + tail.cost⟩

def factor (ask : Nat → Nat → Bool) (n : Nat) (queryCost : Nat → Nat := unitCost) : Run (List Nat) :=
  factorAux queryCost ask n.log2 n

private theorem log_mul_lower {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    a.log2 + b.log2 ≤ (a*b).log2 := by
  apply (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos ha hb))).2
  rw [Nat.pow_add]
  exact Nat.mul_le_mul (power_log_lower ha) (power_log_lower hb)

structure FactorizationBound (n : Nat) (r : Run (List Nat)) : Prop where
  product_eq : product r.value = n
  all_prime : ∀ p ∈ r.value, IsPrime p
  query_bound : r.cost ≤ 2 * n.log2

private theorem factorAux_correct {ask : Nat → Nat → Bool} (spec : CorrectOracle ask)
    (fuel n : Nat) (hn : 0 < n) (enough : n.log2 ≤ fuel) :
    FactorizationBound n (factorAux unitCost ask fuel n) := by
  induction fuel generalizing n with
  | zero =>
    have n1 : n = 1 := by
      by_cases h : 2 ≤ n
      · have := log_positive h; omega
      · omega
    subst n
    exact ⟨rfl, by simp [factorAux], by simp [factorAux]⟩
  | succ f ih =>
    by_cases tiny : n < 2
    · have n1 : n = 1 := by omega
      subst n
      exact ⟨rfl, by simp [factorAux], by simp [factorAux]⟩
    · have n2 : 2 ≤ n := by omega
      obtain ⟨p, hp⟩ := leastDivisor_exists n2
      have pp : 0 < p := by have := hp.ge_two; omega
      have ppLog := log_positive hp.ge_two
      have qPos := Nat.div_pos (Nat.le_of_dvd hn hp.divides) pp
      have decomp := Nat.mul_div_cancel' hp.divides
      have save := log_mul_lower pp qPos
      rw [decomp] at save
      have tail := ih (n / p) qPos (by omega)
      have head := firstFactor_correct spec n2 hp
      simp only [factorAux, if_neg tiny, head]
      refine ⟨?_, ?_, ?_⟩
      · change p * product (factorAux unitCost ask f (n / p)).value = n
        rw [tail.product_eq, decomp]
      · intro x hx
        rcases List.mem_cons.mp hx with e | h
        · exact e ▸ hp.prime
        · exact tail.all_prime x h
      · have := tail.query_bound
        change 2 * p.log2 + (factorAux unitCost ask f (n / p)).cost ≤ 2 * n.log2
        omega

/-- The complete list multiplies to n, every item is prime, and the total
number of oracle calls for the whole list is at most twice floor(log₂ n). -/
theorem factor_correct {ask : Nat → Nat → Bool} (spec : CorrectOracle ask)
    {n : Nat} (hn : 0 < n) : FactorizationBound n (factor ask n) :=
  factorAux_correct spec n.log2 n hn (Nat.le_refl _)


/-! ## Using a complete factorization to answer a threshold query -/

private theorem IsPrime.divides_left_or_right {p a b : Nat} (hp : IsPrime p)
    (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  obtain ⟨u, v, hu, hv, uv⟩ := Nat.dvd_mul.mp h
  by_cases one : u = 1
  · subst u
    simp only [Nat.one_mul] at uv
    exact Or.inr (uv ▸ hv)
  · have nonzero : u ≠ 0 := by
      intro zero
      rw [zero, Nat.zero_mul] at uv
      have := hp.1
      omega
    have eq := hp.2 u (by omega) ⟨v, uv.symm⟩
    exact Or.inl (eq ▸ hu)

private theorem member_divides_product {p : Nat} {ps : List Nat} (mem : p ∈ ps) :
    p ∣ product ps := by
  induction ps with
  | nil => simp at mem
  | cons a rest ih =>
    change p ∣ a * product rest
    rcases List.mem_cons.mp mem with same | later
    · subst a
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih later) (Nat.dvd_mul_left _ _)

private theorem prime_dividing_product_is_member {p : Nat} (hp : IsPrime p) (ps : List Nat)
    (primes : ∀ x ∈ ps, IsPrime x) (divides : p ∣ product ps) : p ∈ ps := by
  induction ps with
  | nil =>
    have := Nat.eq_one_of_dvd_one divides
    have := hp.1
    omega
  | cons a rest ih =>
    rcases hp.divides_left_or_right divides with first | later
    · exact List.mem_cons.mpr (.inl ((primes a (by simp)).2 p hp.1 first))
    · exact List.mem_cons.mpr (.inr (ih (fun x hx => primes x (by simp [hx])) later))

/-- The reverse reduction is a scan of the prime factor list. -/
theorem query_from_factors {n k : Nat} {ps : List Nat} (hProduct : product ps = n)
    (hPrimes : ∀ x ∈ ps, IsPrime x) :
    HasDivisor n k ↔ ∃ p ∈ ps, p ≤ k := by
  subst n
  constructor
  · rintro ⟨d, hd, hk, hdvd⟩
    obtain ⟨p, hp⟩ := leastDivisor_exists hd
    have mem := prime_dividing_product_is_member hp.prime ps hPrimes
      (Nat.dvd_trans hp.divides hdvd)
    exact ⟨p, mem, Nat.le_trans (Nat.le_of_dvd (by omega) hp.divides) hk⟩
  · rintro ⟨p, mem, hpk⟩
    exact ⟨p, (hPrimes p mem).1, hpk, member_divides_product mem⟩

/-! ## A concrete oracle and the work inside a query -/

def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

private theorem divides_factorial {d : Nat} (hd : 0 < d) (k : Nat) (hk : d ≤ k) :
    d ∣ factorial k := by
  induction k with
  | zero => omega
  | succ i ih =>
    by_cases same : d = i + 1
    · subst d
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left _ _)

private theorem prime_dividing_factorial_le {p : Nat} (hp : IsPrime p) (k : Nat)
    (h : p ∣ factorial k) : p ≤ k := by
  induction k with
  | zero =>
    have := Nat.eq_one_of_dvd_one h
    have := hp.1
    omega
  | succ i ih =>
    rcases hp.divides_left_or_right h with last | earlier
    · exact Nat.le_of_dvd (by omega) last
    · have := ih earlier
      omega

theorem factorial_gcd_iff {n k : Nat} (hn : 0 < n) :
    1 < n.gcd (factorial k) ↔ HasDivisor n k := by
  constructor
  · intro big
    obtain ⟨p, hp⟩ := leastDivisor_exists big
    have pn := Nat.dvd_trans hp.divides (Nat.gcd_dvd_left n (factorial k))
    have pf := Nat.dvd_trans hp.divides (Nat.gcd_dvd_right n (factorial k))
    exact ⟨p, hp.ge_two, prime_dividing_factorial_le hp.prime k pf, pn⟩
  · rintro ⟨d, hd, hk, hdvd⟩
    have common := Nat.dvd_gcd hdvd (divides_factorial (by omega) k hk)
    have positive := Nat.gcd_pos_of_pos_left (factorial k) hn
    have := Nat.le_of_dvd positive common
    omega

structure ModularProduct where
  residue : Nat
  multiplications : Nat
  deriving Repr, DecidableEq

/-- The direct modular recurrence evaluates one product for each successor. -/
def factorialMod (n : Nat) : Nat → ModularProduct
  | 0 => ⟨1 % n, 0⟩
  | k + 1 =>
    let prev := factorialMod n k
    ⟨(k + 1) * prev.residue % n, prev.multiplications + 1⟩

theorem factorialMod_exact (n k : Nat) :
    factorialMod n k = ⟨factorial k % n, k⟩ := by
  induction k with
  | zero => rfl
  | succ i ih => simp [factorialMod, ih, factorial, Nat.mul_mod_mod]

def factorialOracle (n k : Nat) : Bool :=
  decide (1 < n.gcd (factorialMod n k).residue)

theorem factorialOracle_correct : CorrectOracle factorialOracle := by
  intro n k hn
  have g : n.gcd (factorial k % n) = n.gcd (factorial k) :=
    (Nat.gcd_comm _ _).trans (Nat.gcd_rec n (factorial k)).symm
  simpa [factorialOracle, factorialMod_exact, g] using (factorial_gcd_iff (n := n) (k := k) (by omega))

/-- This unconditional algorithm is correct. The bound counts threshold queries. -/
theorem factor_with_factorials {n : Nat} (hn : 0 < n) :
    FactorizationBound n (factor factorialOracle n) :=
  factor_correct factorialOracle_correct hn

/-- Identify the first successful bracketing query without tracing any test inputs. -/
theorem first_yes_endpoint {n p : Nat} (hn : 2 ≤ n) (hp : LeastDivisor n p) :
    factorialOracle n (2 ^ (p.log2 + 1) - 1) = true ∧
    ∀ j, j < p.log2 → factorialOracle n (2 ^ (j + 1) - 1) = false := by
  have pp : 0 < p := by have := hp.ge_two; omega
  have threshold := fun k => (factorialOracle_correct n k hn).trans (hp.threshold k)
  constructor
  · apply (threshold _).2
    have : p < 2 ^ (p.log2 + 1) := (Nat.log2_lt (by omega)).1 (by omega)
    omega
  · intro j hj
    apply noAnswer
    intro h
    have := (threshold _).1 h
    have low := power_log_lower pp
    have mono := Nat.pow_le_pow_right (by decide : 0 < 2) (show j + 1 ≤ p.log2 by omega)
    have pos := Nat.two_pow_pos (j + 1)
    omega

theorem least_of_semiprime {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) (order : p ≤ q) :
    LeastDivisor (p*q) p := by
  have prodPos := Nat.mul_pos (show 0 < p by have := hp.1; omega)
    (show 0 < q by have := hq.1; omega)
  have pd := Nat.dvd_mul_right p q
  have large := Nat.le_trans hp.1 (Nat.le_of_dvd prodPos pd)
  obtain ⟨l, hl⟩ := leastDivisor_exists large
  have lp := hl.least p hp.1 pd
  have same : l = p := by
    rcases hl.prime.divides_left_or_right hl.divides with left | right
    · exact hp.2 l hl.ge_two left
    · have := hq.2 l hl.ge_two right
      omega
  exact same ▸ hl

/-- On a semiprime p*q with p ≤ q ≤ 2p, even the first successful query
of the direct implementation costs w multiplications with p*q ≤ 2*w². -/
theorem direct_product_cost {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (order : p ≤ q) (balanced : q ≤ 2 * p) :
    let n := p*q
    let k := 2 ^ (p.log2 + 1) - 1
    let w := (factorialMod n k).multiplications
    factorialOracle n k = true ∧ p ≤ w ∧ n ≤ 2 * w^2 := by
  dsimp only
  let n := p*q
  let k := 2 ^ (p.log2 + 1) - 1
  have hleast := least_of_semiprime hp hq order
  have pos := Nat.mul_pos (show 0 < p by have := hp.1; omega)
    (show 0 < q by have := hq.1; omega)
  have large : 2 ≤ n := Nat.le_trans hp.1 (Nat.le_of_dvd pos hleast.divides)
  have yes := (first_yes_endpoint large hleast).1
  have pk : p ≤ k := (hleast.threshold k).mp ((factorialOracle_correct n k large).mp yes)
  have qk : q ≤ 2*k := by omega
  have bound := Nat.mul_le_mul pk qk
  have rearrange : k * (2*k) = 2*k^2 := by simp [Nat.pow_two, Nat.mul_left_comm]
  rw [rearrange] at bound
  change factorialOracle n k = true ∧ p ≤ (factorialMod n k).multiplications ∧
    n ≤ 2 * (factorialMod n k).multiplications ^ 2
  rw [factorialMod_exact]
  exact ⟨yes, pk, bound⟩

/-! ## Arbitrarily large instances exceeding every polynomial budget -/

private theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ k ih => exact Nat.mul_pos (by omega) ih

/-- Euclid's construction supplies a prime above any prescribed cutoff. -/
private theorem prime_above (limit : Nat) : ∃ p, IsPrime p ∧ limit < p := by
  have positive := factorial_pos limit
  obtain ⟨p, hp⟩ := leastDivisor_exists (n := factorial limit + 1) (by omega)
  refine ⟨p, hp.prime, ?_⟩
  by_cases short : p ≤ limit
  · have divides := divides_factorial (d := p) (by have := hp.ge_two; omega) limit short
    have one := Nat.eq_one_of_dvd_one ((Nat.dvd_add_iff_right divides).mpr hp.divides)
    have := hp.ge_two
    omega
  · omega

private theorem square_le_exp (t : Nat) (ht : 4 ≤ t) : t*t ≤ 2^t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction u with
  | zero => decide
  | succ u ih =>
    change ((4 + u) + 1) * ((4 + u) + 1) ≤ 2 ^ ((4 + u) + 1)
    rw [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    have linear : 2*(4+u) + 1 ≤ (4+u)*(4+u) := by
      have h := Nat.mul_le_mul_right (4+u) (show 3 ≤ 4+u by omega)
      omega
    omega

/-- An explicit eventual domination bound for the binary input-length estimate below. -/
private theorem exponent_dominates (c d x : Nat) (large : 2^(c+2*d+4) ≤ x) :
    c * (2*(x+1))^d < 2^x := by
  have xp : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) large
  let t := x.log2
  have tLarge : c+2*d+4 ≤ t := (Nat.le_log2 (by omega)).2 large
  have tLower : 2^t ≤ x := power_log_lower xp
  have tUpper : x < 2^(t+1) := (Nat.log2_lt (by omega)).1 (by dsimp [t]; omega)
  have step : 2*(x+1) ≤ 2^(t+2) := by
    rw [show t+2 = (t+1)+1 by omega, Nat.pow_succ]
    omega
  have degrees := Nat.mul_le_mul_right t (show d+1 ≤ t by omega)
  rw [Nat.add_mul, Nat.one_mul] at degrees
  have sq := square_le_exp t (by omega)
  have expBound : c + (t+2)*d ≤ x := by
    rw [Nat.add_mul, Nat.mul_comm t d]
    omega
  have productBound := Nat.mul_lt_mul_of_lt_of_le
    (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left step d)
    (Nat.pow_pos (Nat.two_pow_pos (t+2)))
  calc
    c * (2*(x+1))^d < 2^c * (2^(t+2))^d := productBound
    _ = 2^(c+(t+2)*d) := by
      rw [Nat.pow_add 2 c ((t+2)*d), Nat.pow_mul 2 (t+2) d]
    _ ≤ 2^x := Nat.pow_le_pow_right (by decide) expBound

private theorem square_bits_upper {p : Nat} (hp : 0 < p) :
    (p*p).log2 + 1 ≤ 2*(p.log2+1) := by
  have upper : p < 2^(p.log2+1) := (Nat.log2_lt (by omega)).1 (by omega)
  have sq := Nat.mul_lt_mul_of_lt_of_le upper (Nat.le_of_lt upper) (Nat.two_pow_pos _)
  have h : p*p < 2^(2*(p.log2+1)) := by
    rw [Nat.mul_comm 2 (p.log2+1), Nat.pow_mul, Nat.pow_two]
    exact sq
  have := (Nat.log2_lt (Nat.ne_of_gt (Nat.mul_pos hp hp))).2 h
  omega

/-- For any constant, degree, and minimum input length there is a prime square
on which one bracketing query of the sequential implementation already uses
more than c * (input bit length)^d modular multiplications. -/
theorem direct_exceeds_every_polynomial (c d minBits : Nat) :
    ∃ p, IsPrime p ∧ minBits ≤ (p*p).log2 + 1 ∧
      let n := p*p
      let k := 2^(p.log2+1) - 1
      factorialOracle n k = true ∧
        c * (n.log2+1)^d < (factorialMod n k).multiplications := by
  let limit := 2^(c+2*d+4) + minBits
  obtain ⟨p, hp, big⟩ := prime_above (2^limit)
  have pp : 0 < p := by have := hp.1; omega
  have pl : limit ≤ p.log2 := (Nat.le_log2 (by omega)).2 (Nat.le_of_lt big)
  have size := log_monotone pp (Nat.le_of_dvd (Nat.mul_pos pp pp) (Nat.dvd_mul_right p p))
  have bigLog : 2^(c+2*d+4) ≤ p.log2 := by dsimp [limit] at pl; omega
  have minLimit : minBits ≤ limit := Nat.le_add_left _ _
  have minimum : minBits ≤ (p*p).log2+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_trans minLimit pl) size) (Nat.le_succ _)
  have cost := direct_product_cost hp hp (Nat.le_refl p) (by omega)
  have growth := exponent_dominates c d p.log2 bigLog
  have compared := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (square_bits_upper pp) d)
  refine ⟨p, hp, minimum, cost.1, ?_⟩
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt compared growth)
    (Nat.le_trans (power_log_lower pp) cost.2.1)

/-! ## Charge the whole execution for modular multiplications -/

private theorem bisect_value_independent (queryCost : Nat → Nat) (ask : Nat → Bool)
    (depth lo : Nat) :
    (bisect queryCost ask lo depth).value = (bisect unitCost ask lo depth).value := by
  induction depth generalizing lo with
  | zero => rfl
  | succ d ih =>
    cases h : ask (lo + 2^d - 1) <;> simp [bisect, query, h, ih]

private theorem bracket_value_independent (queryCost : Nat → Nat) (ask : Nat → Bool)
    (fuel level : Nat) :
    (bracket queryCost ask level fuel).value = (bracket unitCost ask level fuel).value := by
  induction fuel generalizing level with
  | zero => rfl
  | succ f ih =>
    cases h : ask (2^(level+1) - 1) <;>
      simp [bracket, query, h, ih, bisect_value_independent queryCost]

/-- Changing the cost charged at a query leaves the returned factor list identical. -/
theorem factor_value_independent (queryCost : Nat → Nat) (ask : Nat → Nat → Bool) (n : Nat) :
    (factor ask n queryCost).value = (factor ask n).value := by
  have aux (fuel m : Nat) :
      (factorAux queryCost ask fuel m).value = (factorAux unitCost ask fuel m).value := by
    induction fuel generalizing m with
    | zero => rfl
    | succ f ih =>
      by_cases tiny : m < 2
      · simp [factorAux, tiny]
      · have head : (firstFactor queryCost ask m).value = (firstFactor unitCost ask m).value :=
          bracket_value_independent queryCost (ask m) m.log2 1
        simp [factorAux, tiny, head, ih]
  exact aux n.log2 n

private theorem bracket_pays (queryCost : Nat → Nat) {ask : Nat → Bool} {j : Nat}
    (yes : ask (2^(j+1) - 1) = true)
    (earlier : ∀ i, i < j → ask (2^(i+1) - 1) = false) (fuel level : Nat)
    (low : level ≤ j) (enough : j < level+fuel) :
    queryCost (2^(j+1) - 1) ≤ (bracket queryCost ask level fuel).cost := by
  induction fuel generalizing level with
  | zero => omega
  | succ f ih =>
    by_cases here : level = j
    · subst level
      simp [bracket, query, yes]
    · have before : level < j := by omega
      have tail := ih (level+1) (by omega) (by omega)
      simpa [bracket, query, earlier level before] using
        Nat.le_trans tail (Nat.le_add_right _ (queryCost (2^(level+1)-1)))

/-- The bracketing endpoint is actually visited and charged by the full factorization. -/
theorem factor_pays_for_first_yes {n p : Nat} (hn : 2 ≤ n) (hp : LeastDivisor n p)
    (queryCost : Nat → Nat) :
    queryCost (2^(p.log2+1)-1) ≤ (factor factorialOracle n queryCost).cost := by
  obtain ⟨yes, earlier⟩ := first_yes_endpoint hn hp
  have pp : 0 < p := by have := hp.ge_two; omega
  have lp := log_positive hp.ge_two
  have le := log_monotone pp (Nat.le_of_dvd (by omega : 0 < n) hp.divides)
  have head : queryCost (2^(p.log2+1)-1) ≤ (firstFactor queryCost factorialOracle n).cost :=
    bracket_pays queryCost yes earlier n.log2 1 (by omega) (by omega)
  unfold factor
  cases h : n.log2 with
  | zero =>
    have := log_positive hn
    omega
  | succ f =>
    simp only [factorAux, if_neg (show ¬ n < 2 by omega)]
    exact Nat.le_trans head (Nat.le_add_right _ _)

/-- End-to-end lower bound for the number of modular multiplications over all
sequential factorial evaluations along the actual execution path. -/
theorem full_run_exceeds_every_polynomial (c d minBits : Nat) :
    ∃ p, IsPrime p ∧ minBits ≤ (p*p).log2 + 1 ∧
      c * ((p*p).log2+1)^d < (factor factorialOracle (p*p) id).cost := by
  obtain ⟨p, hp, size, _, high⟩ := direct_exceeds_every_polynomial c d minBits
  have least := least_of_semiprime hp hp (Nat.le_refl _)
  have pp : 0 < p := by have := hp.1; omega
  have large := Nat.le_trans hp.1 (Nat.le_of_dvd (Nat.mul_pos pp pp) least.divides)
  have paid := factor_pays_for_first_yes large least id
  rw [factorialMod_exact] at high
  exact ⟨p, hp, size, Nat.lt_of_lt_of_le high paid⟩

-- Concrete checks include the empty factorization, repetitions and a semiprime.
#guard factor factorialOracle 1 = ⟨[], 0⟩
#guard factor factorialOracle 84 = ⟨[2, 2, 3, 7], 10⟩
#guard factor factorialOracle 91 = ⟨[7, 13], 10⟩
#guard factor factorialOracle 97 = ⟨[97], 12⟩
#guard factor factorialOracle 91 id = ⟨[7, 13], 82⟩

#print axioms factor_correct
#print axioms query_from_factors
#print axioms factor_with_factorials
#print axioms direct_product_cost
#print axioms direct_exceeds_every_polynomial
#print axioms factor_value_independent
#print axioms full_run_exceeds_every_polynomial

end FactorizationThreshold
