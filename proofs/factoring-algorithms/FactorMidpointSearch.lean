import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Factoring by the odd part of a factor sum or difference

Let N be a product of two distinct odd primes p and q, let b be its binary
length, and fix a nonnegative integer c. Remove all powers of two from
p+q and |p-q|. If either odd part is at most N^(1/4) b^c, the search
in this file splits N in deterministic polynomial time from N alone.
The function also handles even composites immediately.

* `DyadicMidpoint.factorForExponent` runs the search for a fixed c.
* `DyadicMidpoint.factorForExponent_sound` proves every answer is a proper split.
* `DyadicMidpoint.factorForExponent_succeeds` proves the finite search guarantee.
* `SmallMultipliers.partner_count` bounds the coverage of small multipliers.
* `FactorSumSieve.rejecting_requires_rows` bounds complete modular tables.

The running-time deduction uses the four-root bound explained below and
standard bit costs. The code contains no machine-level time model.
-/

/-!
## A midpoint search with power-of-two steps

For an odd product N with midpoint a and half-gap d, write d = 2^t u.
Then a² = N + 2^(2t) u². The midpoint lies in a square-root class
modulo M = 2^(2t). Inside each such class we step by M. We try all
exponents t up to log₂ N, so the input to the search supplies no hint.

There is also a complementary search. If instead a = 2^t u, the
half-gap d is a square root of -N modulo M. From a² = N+d² and
2 sqrt(N) d ≤ N+d², we get d/M ≤ u²/(2 sqrt(N)). This search
starts at zero. Either a small odd part of the half-gap or a small
odd part of the midpoint suffices.

For odd N there are at most four roots at every precision. If r is one
root and x is another, 2^k divides (x-r)(x+r). For k ≥ 3 exactly one
of x-r and x+r is 2 modulo 4, hence x is ±r modulo 2^(k-1). This
gives at most four residues modulo 2^k. The smaller precisions are
immediate. The binary lifting routine below computes this list from N.

For b the binary length of N and any fixed c ≥ 0, the promise
u ≤ N^(1/4) b^c gives u² ≤ (floor(sqrt N)+1) b^(2c).
The finite search theorems below therefore give a deterministic
polynomial bit bound on this family. We compute O(b) root lists with
O(b) lifting levels each and at most 4*(b^(2c)+2) candidates per list.
The integer arithmetic takes polynomially many bit operations on
O(b+c log b)-bit integers. This bit-cost accounting and the four-root
count are mathematical arguments; the finite search guarantee is
checked below. A square N can also be recognized directly.

Steinfeld and Zheng (2001), proof of Theorem 3, derive the doubled
precision of the factor sum from shared low bits and give the
four-root lifting bound: https://doi.org/10.1007/3-540-45353-9_5 .
For the modular factor-sum sieve, see Hittmeir (2023),
https://doi.org/10.1016/j.jnt.2023.02.010 , and Stănică, Mulder and
Hittmeir (2026), https://arxiv.org/abs/2606.13018 .
-/

namespace DyadicMidpoint

/-- List all square roots of N modulo 2^k by lifting one bit at a time. -/
def roots (N : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | k+1 =>
    let m := 2^k
    ((roots N k).flatMap fun r => [r, r+m]).filter
      fun x => decide (x^2 % (m*2) = N % (m*2))

/-- Each true root occurs in the list of canonical representatives. -/
theorem root_complete (N k x : ℕ) (hx : x^2 ≡ N [MOD 2^k]) :
    x % (2^k) ∈ roots N k := by
  induction k with
  | zero => simp [roots, Nat.mod_one]
  | succ k ih =>
    let m : ℕ := 2^k
    have hm : 0 < m := by dsimp [m]; positivity
    have hdiv : m ∣ m*2 := dvd_mul_right _ _
    have he : x^2 ≡ N [MOD m*2] := by simpa [m, pow_succ] using hx
    have hr := ih (he.of_dvd hdiv)
    change x % m ∈ roots N k at hr
    let v := x % (m*2)
    have hv : v < m*2 := Nat.mod_lt _ (by omega)
    have hvmod : v % m = x % m := Nat.mod_mod_of_dvd _ hdiv
    have hcase : v = x%m ∨ v = x%m+m := by
      by_cases h : v < m
      · left
        rwa [Nat.mod_eq_of_lt h] at hvmod
      · right
        have hh : v-m < m := by omega
        rw [Nat.mod_eq_sub_mod (by omega : m ≤ v), Nat.mod_eq_of_lt hh] at hvmod
        omega
    rw [pow_succ]
    change v ∈ ((roots N k).flatMap fun r => [r, r+m]).filter _
    apply List.mem_filter.mpr
    refine ⟨List.mem_flatMap.mpr ⟨x%m, hr, by simpa using hcase⟩, ?_⟩
    apply decide_eq_true
    exact ((Nat.mod_modEq x (m*2)).pow 2).trans he

/-- Search a bounded number of consecutive blocks for every possible t. -/
def midpoints (N rounds : ℕ) : List ℕ :=
  let start := N.sqrt
  (List.range (N.log2+1)).flatMap fun t =>
    let M := 2^(2*t)
    let rs := roots N (2*t)
    (List.range rounds).flatMap fun j =>
      rs.map fun r => (start/M+j)*M+r

/-- When the midpoint is divisible by 2^t, enumerate half-gaps in the
root classes of -N and convert each trial back to a trial midpoint. -/
def midpointsFromGaps (N rounds : ℕ) : List ℕ :=
  (List.range (N.log2+1)).flatMap fun t =>
    let M := 2^(2*t)
    let rs := roots (M-N%M) (2*t)
    (List.range rounds).flatMap fun j =>
      rs.map fun r => (N+(j*M+r)^2).sqrt

def atMidpoint (N a : ℕ) : Option (ℕ × ℕ) :=
  let d := (a^2-N).sqrt
  if 1 < a-d ∧ 1 < a+d ∧ (a-d)*(a+d) = N then some (a-d, a+d) else none

def factorWithin (N rounds : ℕ) : Option (ℕ × ℕ) :=
  (midpoints N rounds ++ midpointsFromGaps N rounds).findSome? (atMidpoint N)

private theorem true_midpoint_works {N a d : ℕ} (hgap : a^2 = N+d^2)
    (hproper : 1 < a-d ∧ 1 < a+d ∧ (a-d)*(a+d) = N) :
    (atMidpoint N a).isSome := by
  have hsq : (a^2-N).sqrt = d := by simp [hgap, Nat.sqrt_eq']
  simp [atMidpoint, hsq, hproper]

/-- Every reported pair consists of proper factors. -/
theorem factorWithin_sound {N rounds : ℕ} {f : ℕ × ℕ}
    (hf : factorWithin N rounds = some f) :
    1 < f.1 ∧ 1 < f.2 ∧ f.1*f.2 = N := by
  obtain ⟨a, _, ha⟩ := List.exists_of_findSome?_eq_some hf
  dsimp [atMidpoint] at ha
  split at ha
  · rename_i h
    cases ha
    exact h
  · contradiction

/-- A square gap of M*u² places a within the first K+2 blocks. -/
theorem block_bound {N a M u K : ℕ} (hM : 0 < M)
    (ha : a^2 = N + M*u^2) (hu : u^2 ≤ (N.sqrt+1)*K) :
    a/M < N.sqrt/M + K+2 := by
  let s := N.sqrt
  have hs : N < (s+1)^2 := Nat.lt_succ_sqrt' _
  have htop : s+1 ≤ (s/M+1)*M := by
    have hd := Nat.div_add_mod s M
    have hr := Nat.mod_lt s hM
    rw [add_mul, one_mul, Nat.mul_comm (s/M) M]
    omega
  by_contra! h
  have hmul : (s/M+K+2)*M ≤ a := (Nat.le_div_iff_mul_le hM).mp h
  have hbase : (s/M+1)*M + (K+1)*M ≤ a := by
    calc
      _ = (s/M+K+2)*M := by ring
      _ ≤ a := hmul
  have hh := (Nat.add_le_add_right htop ((K+1)*M)).trans hbase
  have hsq := Nat.pow_le_pow_left hh 2
  have hub : M*u^2 ≤ M*((s+1)*K) := Nat.mul_le_mul_left M hu
  have hc := Nat.mul_le_mul_left (s+1) (Nat.mul_le_mul_right M (Nat.le_succ K))
  have lower : (s+1)^2+M*((s+1)*K) ≤ (s+1+(K+1)*M)^2 := calc
    _ = (s+1)^2 + (s+1)*(K*M) := by ring
    _ ≤ (s+1)^2 + (s+1)*((K+1)*M) := Nat.add_le_add_left hc _
    _ = (s+1)*(s+1+(K+1)*M) := by ring
    _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have upper : a^2 < (s+1)^2 + M*((s+1)*K) := by
    rw [ha]
    exact Nat.add_lt_add_of_lt_of_le hs hub
  exact (not_lt_of_ge (lower.trans hsq)) upper

/-- Executable search succeeds for any proper pair with the specified half-gap.
The hypotheses give a finite, integer-only certificate for the search budget. -/
theorem factorWithin_succeeds {N a d t u K : ℕ}
    (ht : t ≤ N.log2) (hd : d = 2^t*u) (hgap : a^2 = N+d^2)
    (hproper : 1 < a-d ∧ 1 < a+d ∧ (a-d)*(a+d) = N)
    (hu : u^2 ≤ (N.sqrt+1)*K) : (factorWithin N (K+2)).isSome := by
  let M : ℕ := 2^(2*t)
  have hM : 0 < M := by dsimp [M]; positivity
  have hd' : d^2 = M*u^2 := by
    rw [hd, mul_pow]
    dsimp [M]
    rw [← pow_mul, Nat.mul_comm t 2]
  have ha : a^2 = N + M*u^2 := hgap.trans (by rw [hd'])
  have hx : a^2 ≡ N [MOD M] := by
    rw [ha]
    exact Nat.add_modulus_mul_modEq_iff.mpr (Nat.ModEq.refl _)
  have hroot := root_complete N (2*t) a hx
  have hs : N.sqrt ≤ a := by
    by_contra! h
    have e := Nat.pow_le_pow_left (show a+1 ≤ N.sqrt from h) 2
    have g := Nat.sqrt_le' N
    nlinarith
  have hdiv : N.sqrt/M ≤ a/M := Nat.div_le_div_right hs
  let j := a/M - N.sqrt/M
  have hj : j < K+2 := by
    have h := block_bound hM ha hu
    dsimp [j]
    omega
  have ha' : (N.sqrt/M+j)*M+a%M = a := by
    rw [show N.sqrt/M+j = a/M from Nat.add_sub_of_le hdiv,
      Nat.mul_comm (a/M) M, Nat.div_add_mod]
  have hmem : a ∈ midpoints N (K+2) := by
    apply List.mem_flatMap.mpr
    refine ⟨t, List.mem_range.mpr (by omega), List.mem_flatMap.mpr ?_⟩
    exact ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨a%M, hroot, ha'⟩⟩
  apply List.findSome?_isSome_iff.mpr
  exact ⟨a, List.mem_append_left _ hmem, true_midpoint_works hgap hproper⟩

/-- Complementary guarantee when the *midpoint* has a small odd part. -/
theorem factorWithin_succeeds_from_sum {N a d t u K : ℕ} (hN : 0 < N)
    (ht : t ≤ N.log2) (hmid : a = 2^t*u) (hgap : a^2 = N+d^2)
    (hproper : 1 < a-d ∧ 1 < a+d ∧ (a-d)*(a+d) = N)
    (hu : u^2 ≤ (N.sqrt+1)*K) : (factorWithin N (K+2)).isSome := by
  let M : ℕ := 2^(2*t)
  have hM : 0 < M := by dsimp [M]; positivity
  have ha : a^2 = M*u^2 := by
    rw [hmid, mul_pow]
    dsimp [M]
    rw [← pow_mul, Nat.mul_comm t 2]
  have hx : d^2 ≡ M-N%M [MOD M] := by
    have hz : N+d^2 ≡ 0 [MOD M] := by rw [← hgap, ha]; simp [Nat.ModEq]
    have hr : N+(M-N%M) ≡ 0 [MOD M] := calc
      _ ≡ N%M+(M-N%M) [MOD M] := (Nat.mod_modEq N M).symm.add_right _
      _ = M := Nat.add_sub_of_le (Nat.mod_lt _ hM).le
      _ ≡ 0 [MOD M] := by simp [Nat.ModEq]
    exact Nat.ModEq.add_left_cancel' N (hz.trans hr.symm)
  have hs : 0 < N.sqrt := Nat.sqrt_pos.mpr hN
  have ham : 2*N.sqrt*d ≤ N.sqrt^2+d^2 := by
    have h : 2*(N.sqrt : ℤ)*(d : ℤ) ≤ (N.sqrt : ℤ)^2+(d : ℤ)^2 := by
      nlinarith [sq_nonneg ((N.sqrt : ℤ)-(d : ℤ))]
    exact_mod_cast h
  have hprod : (2*N.sqrt)*d ≤ (2*N.sqrt)*(M*K) := calc
    _ ≤ N.sqrt^2+d^2 := ham
    _ ≤ N+d^2 := Nat.add_le_add_right (Nat.sqrt_le' _) _
    _ = M*u^2 := hgap.symm.trans ha
    _ ≤ M*((N.sqrt+1)*K) := Nat.mul_le_mul_left _ hu
    _ ≤ M*((2*N.sqrt)*K) :=
      Nat.mul_le_mul_left M (Nat.mul_le_mul_right K (by omega))
    _ = _ := by ring
  have hd : d ≤ M*K := Nat.le_of_mul_le_mul_left hprod (by omega)
  have hj : d/M ≤ K := calc
    _ ≤ (M*K)/M := Nat.div_le_div_right hd
    _ = _ := by simp [hM.ne']
  have hroot := root_complete (M-N%M) (2*t) d hx
  have hmem : a ∈ midpointsFromGaps N (K+2) := by
    apply List.mem_flatMap.mpr
    refine ⟨t, List.mem_range.mpr (by omega), List.mem_flatMap.mpr ?_⟩
    refine ⟨d/M, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨d%M, hroot, ?_⟩⟩
    change (N+(d/M*M+d%M)^2).sqrt = a
    rw [Nat.mul_comm (d/M) M, Nat.div_add_mod, ← hgap, Nat.sqrt_eq']
  apply List.findSome?_isSome_iff.mpr
  exact ⟨a, List.mem_append_right _ hmem, true_midpoint_works hgap hproper⟩

/-- One fixed-exponent promise algorithm. The input supplies no factor bits. -/
def factorForExponent (N c : ℕ) : Option (ℕ × ℕ) :=
  if N < 4 then none
  else if N % 2 = 0 then some (2, N/2)
  else factorWithin N ((N.log2+1)^(2*c)+2)

theorem factorForExponent_sound {N c : ℕ} {f : ℕ × ℕ}
    (hf : factorForExponent N c = some f) : 1 < f.1 ∧ 1 < f.2 ∧ f.1*f.2 = N := by
  unfold factorForExponent at hf
  split at hf
  · contradiction
  · split at hf
    · cases hf
      change 1 < 2 ∧ 1 < N/2 ∧ 2*(N/2) = N
      exact ⟨by decide, by omega, by omega⟩
    · exact factorWithin_sound hf

/-- On a semiprime, every reported split is its complete prime factorization. -/
theorem factorForExponent_semiprime {p q c : ℕ} {f : ℕ × ℕ}
    (hp : p.Prime) (hq : q.Prime) (hf : factorForExponent (p*q) c = some f) :
    (f.1 = p ∧ f.2 = q) ∨ (f.1 = q ∧ f.2 = p) := by
  obtain ⟨hx, hy, hxy⟩ := factorForExponent_sound hf
  have orient {x y : ℕ} (h : x*y = p*q) (hproper : 1 < y) (hd : p ∣ x) :
      x = p ∧ y = q := by
    obtain ⟨k, rfl⟩ := hd
    have hk : k*y = q := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa [Nat.mul_assoc] using h)
    have hdiv : y ∣ q := by rw [← hk]; exact dvd_mul_left _ _
    have he : y = q := ((Nat.dvd_prime hq).mp hdiv).resolve_left (by omega)
    exact ⟨Nat.eq_of_mul_eq_mul_right hq.pos (by simpa [he] using h), he⟩
  have hd : p ∣ f.1*f.2 := by rw [hxy]; exact dvd_mul_right _ _
  rcases hp.dvd_mul.mp hd with h | h
  · exact Or.inl (orient hxy hy h)
  · exact Or.inr (orient ((Nat.mul_comm _ _).trans hxy) hx h).symm

/-- The two searches together, directly on the factors p and p+2*d.
No primality assumption is needed to guarantee a proper split. -/
theorem factorForExponent_succeeds {p d t u c : ℕ} (hp : 1 < p) (hu0 : 0 < u)
    (hside : d = 2^t*u ∨ p+d = 2^t*u)
    (hu : u^2 ≤ ((p*(p+2*d)).sqrt+1) * ((p*(p+2*d)).log2+1)^(2*c)) :
    (factorForExponent (p*(p+2*d)) c).isSome := by
  let N := p*(p+2*d)
  have hN : 0 < N := by dsimp [N]; positivity
  have hfour : 4 ≤ N := calc
    4 = 2*2 := by decide
    _ ≤ p*(p+2*d) := Nat.mul_le_mul hp (by omega)
  change (factorForExponent N c).isSome
  rw [factorForExponent, if_neg (by omega : ¬ N < 4)]
  split
  · rfl
  have hgap : (p+d)^2 = N+d^2 := by dsimp [N]; ring
  have hproper : 1 < p+d-d ∧ 1 < p+d+d ∧ (p+d-d)*(p+d+d) = N := by
    rw [Nat.add_sub_cancel]
    exact ⟨hp, by omega, by dsimp [N]; ring⟩
  have hb : p+d ≤ N := calc
    _ ≤ p+2*d := by omega
    _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  have hpow : 2^t ≤ 2^t*u := Nat.le_mul_of_pos_right _ hu0
  rcases hside with h | h
  · have ht : t ≤ N.log2 := (Nat.le_log2 hN.ne').mpr (by omega)
    exact factorWithin_succeeds ht h hgap hproper hu
  · have ht : t ≤ N.log2 := (Nat.le_log2 hN.ne').mpr (by omega)
    exact factorWithin_succeeds_from_sum hN ht h hgap hproper hu

-- The midpoint 951 lies 112 integers above the initial ceiling 839.
#guard factorForExponent 703697 0 == some (503, 1399)
-- Here the midpoint is 1280 = 2^8 * 5 and the half-gap is 759.
#guard factorForExponent 1062319 0 == some (521, 2039)
-- A fixed budget can exhaust both lists on a composite outside the promise.
#guard factorForExponent 24139 0 == none

end DyadicMidpoint

/-!
## Coverage after allowing small multipliers

Allow any 1 ≤ a < A, 1 ≤ b < B, and ask whether either ap+bq or
|ap-bq| is 2^t u with t < T, u < U. Once p,a,b,t,u are fixed,
at most three q can satisfy these equations. The finite bound counts
all multipliers, including ones a procedure could select after seeing N.

If p,q lie in [X,2X] and A,B are polynomial in log X, then all nonzero
values ap ± bq have t = O(log X). Giving the multiplied input abpq the
same fourth-root allowance permits U = sqrt(X) times a fixed polynomial
in log X. The bound below is then O(sqrt(X) poly(log X)) partners q for
each p. By the prime number theorem there are order X/log X primes in
[X,2X], so the proportion of prime pairs covered by this promise tends
to zero. For distinct primes the zero difference is impossible once
A,B < X. This deduction concerns coverage of these equations.
-/

namespace SmallMultipliers

def possiblePartners (p A B T U : ℕ) : Finset ℕ :=
  (Finset.range A).biUnion fun a => (Finset.range B).biUnion fun b =>
    (Finset.range T).biUnion fun t => (Finset.range U).biUnion fun u =>
      let v := 2^t*u
      {(a*p+v)/b, (a*p-v)/b, (v-a*p)/b}

theorem partner_mem {p q a b t u A B T U : ℕ}
    (ha : a < A) (hb : b < B) (hb0 : 0 < b) (ht : t < T) (hu : u < U)
    (h : b*q = a*p+2^t*u ∨ a*p = b*q+2^t*u ∨ 2^t*u = a*p+b*q) :
    q ∈ possiblePartners p A B T U := by
  apply Finset.mem_biUnion.mpr
  refine ⟨a, Finset.mem_range.mpr ha, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨b, Finset.mem_range.mpr hb, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨t, Finset.mem_range.mpr ht, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨u, Finset.mem_range.mpr hu, ?_⟩
  change q ∈ {(a*p+2^t*u)/b, (a*p-2^t*u)/b, (2^t*u-a*p)/b}
  rcases h with he | he | he
  · simp [← he, hb0.ne']
  · have e : a*p-2^t*u = b*q := by omega
    simp [e, hb0.ne']
  · have e : 2^t*u-a*p = b*q := by omega
    simp [e, hb0.ne']

private theorem range_union_bound (n k : ℕ) (f : ℕ → Finset ℕ)
    (h : ∀ i ∈ Finset.range n, (f i).card ≤ k) :
    ((Finset.range n).biUnion f).card ≤ n*k := by
  simpa using Finset.card_biUnion_le_card_mul (Finset.range n) f k h

theorem partner_count (p A B T U : ℕ) :
    (possiblePartners p A B T U).card ≤ A*(B*(T*(U*3))) := by
  apply range_union_bound
  intro a _
  apply range_union_bound
  intro b _
  apply range_union_bound
  intro t _
  apply range_union_bound
  intro u _
  exact Finset.card_le_three

end SmallMultipliers

/-!
## Testing intervals for a factor sum

For N = p*q, a necessary condition on s = p+q is that, modulo each
chosen prime, s is the sum of a pair with product N. This file studies
a sieve that groups distinct primes and explicitly tabulates the choices
of one allowed residue per prime in each group.

`passes` requires a *single* position in an interval to pass every
prime in a group. Different groups tested separately can use different
positions. The conclusions concern complete tables and full intervals.
-/

namespace FactorSumSieve

/-- Every residue that is the sum of two residues with product N modulo m. -/
def sumResidues (N m : ℕ) : Finset ℕ :=
  (((Finset.range m) ×ˢ (Finset.range m)).filter
    fun z => z.1 * z.2 % m = N % m).image (fun z => (z.1 + z.2) % m)

theorem sum_mem {N m x y : ℕ} (hm : 0 < m) (hxy : x * y % m = N % m) :
    (x + y) % m ∈ sumResidues N m := by
  apply Finset.mem_image.mpr
  refine ⟨(x % m, y % m), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm), Finset.mem_range.mpr (Nat.mod_lt _ hm)⟩
  · simpa only [← Nat.mul_mod] using hxy
  · exact (Nat.add_mod x y m).symm

theorem trivial_sum_mem (N : ℕ) {m : ℕ} (hm : 0 < m) :
    (N + 1) % m ∈ sumResidues N m := sum_mem hm (by simp)

def period (P : Finset ℕ) : ℕ := ∏ l ∈ P, l

/-- Size of a table containing every tuple of locally allowed sums. -/
def rows (N : ℕ) (P : Finset ℕ) : ℕ := ∏ l ∈ P, (sumResidues N l).card

def passes (N lo width : ℕ) (P : Finset ℕ) : Prop :=
  ∃ j < width, ∀ l ∈ P, (lo + j) % l ∈ sumResidues N l

/-- A whole period inside a block guarantees a common position for this group. -/
theorem passes_of_period_le {N lo width : ℕ} {P : Finset ℕ}
    (hP : ∀ l ∈ P, 0 < l) (hwidth : period P ≤ width) : passes N lo width P := by
  have hm : 0 < period P := Finset.prod_pos hP
  let : NeZero (period P) := ⟨hm.ne'⟩
  let z : ZMod (period P) := ((N + 1 : ℕ) : ZMod (period P)) - (lo : ZMod (period P))
  refine ⟨z.val, lt_of_lt_of_le (ZMod.val_lt z) hwidth, ?_⟩
  have hz : lo + z.val ≡ N + 1 [MOD period P] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    dsimp [z]
    ring
  intro l hl
  have hd : l ∣ period P := Finset.dvd_prod_of_mem (fun i : ℕ => i) hl
  rw [show (lo + z.val) % l = (N + 1) % l from hz.of_dvd hd]
  exact trivial_sum_mem _ (hP l hl)

private theorem quadratic_fiber_card {K : Type*} [Field K] [DecidableEq K]
    (R : Finset K) (s n : K) (h : ∀ x ∈ R, x*x + n = s*x) : R.card ≤ 2 := by
  by_cases hn : R.Nonempty
  · obtain ⟨u, hu⟩ := hn
    have inc : R ⊆ {u, s-u} := by
      intro x hx
      have e : (x-u)*(x-(s-u)) = 0 := calc
        _ = (x*x+n-s*x) - (u*u+n-s*u) := by ring
        _ = 0 := by rw [h x hx, h u hu]; ring
      rcases mul_eq_zero.mp e with e | e
      · simp [sub_eq_zero.mp e]
      · simp [sub_eq_zero.mp e]
    exact (Finset.card_le_card inc).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

/-- A prime table must contain at least (l-1)/2 entries. -/
theorem prime_card_lower (N : ℕ) {l : ℕ} (hl : l.Prime) :
    l - 1 ≤ 2 * (sumResidues N l).card := by
  let : Fact l.Prime := ⟨hl⟩
  let D := (Finset.univ : Finset (ZMod l)).erase 0
  let f : ZMod l → ℕ := fun x => (x + (N : ZMod l) / x).val
  have maps : ∀ x ∈ D, f x ∈ sumResidues N l := by
    intro x hx
    have hx' : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have he : x * ((N : ZMod l) / x) = (N : ZMod l) := by
      rw [mul_comm, div_mul_cancel₀ _ hx']
    have hmul := congrArg ZMod.val he
    rw [ZMod.val_mul, ZMod.val_natCast] at hmul
    simpa only [f, ZMod.val_add] using sum_mem hl.pos hmul
  have fibers : ∀ b ∈ sumResidues N l, (D.filter fun x => f x = b).card ≤ 2 := by
    intro b _
    apply quadratic_fiber_card _ (b : ZMod l) (N : ZMod l)
    intro x hx
    obtain ⟨hmem, he⟩ := Finset.mem_filter.mp hx
    have hzero : x ≠ 0 := (Finset.mem_erase.mp hmem).1
    have hcast : x + (N : ZMod l) / x = (b : ZMod l) := by
      simpa only [f, ZMod.natCast_zmod_val] using congrArg (fun t : ℕ => (t : ZMod l)) he
    rw [← hcast, add_mul, div_mul_cancel₀ _ hzero]
  have hcard := Finset.card_le_mul_card_image_of_maps_to maps 2 fibers
  simpa only [D, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod l)), Finset.card_univ,
    ZMod.card] using hcard

private theorem period_per_prime (k a l : ℕ) (ha : 1 ≤ a) (hl : 0 < l)
    (hcard : l - 1 ≤ 2*a) (hlarge : 3^(k+1) ≤ l) : l^k ≤ a^(k+1) := by
  have hthree : l ≤ 3*a := by omega
  have h : l * l^k ≤ l * a^(k+1) := calc
    l * l^k = l^(k+1) := by rw [pow_succ, mul_comm]
    _ ≤ (3*a)^(k+1) := Nat.pow_le_pow_left hthree _
    _ = 3^(k+1) * a^(k+1) := mul_pow _ _ _
    _ ≤ l * a^(k+1) := Nat.mul_le_mul_right _ hlarge
  exact Nat.le_of_mul_le_mul_left h hl

/-- A finite, uniform version of rows ≥ period^(1-o(1)) for squarefree groups.
The constant depends only on the chosen positive precision parameter k. -/
theorem period_pow_le_rows (N k : ℕ) (P : Finset ℕ) (hP : ∀ l ∈ P, l.Prime) :
    (period P)^k ≤ ((3^(k+1))^(3^(k+1)))^k * (rows N P)^(k+1) := by
  let F : ℕ := 3^(k+1)
  let small := P.filter (fun l => l < F)
  let large := P.filter (fun l => ¬ l < F)
  have split : period small * period large = period P :=
    Finset.prod_filter_mul_prod_filter_not P _ _
  have smallSub : small ⊆ Finset.range F := by
    intro l hl
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
  have count : small.card ≤ F := (Finset.card_le_card smallSub).trans_eq (Finset.card_range _)
  have hsmall : period small ≤ F^F := calc
    period small ≤ ∏ _l ∈ small, F :=
      Finset.prod_le_prod' fun l hl => (Finset.mem_filter.mp hl).2.le
    _ = F^small.card := by simp
    _ ≤ F^F := Nat.pow_le_pow_right (by dsimp [F]; positivity) count
  have hentry : ∀ l ∈ P, 1 ≤ (sumResidues N l).card := by
    intro l hl
    exact Finset.card_pos.mpr ⟨_, trivial_sum_mem N (hP l hl).pos⟩
  have hlarge : (period large)^k ≤ (rows N large)^(k+1) := calc
    (period large)^k = ∏ l ∈ large, l^k := by simp [period, Finset.prod_pow]
    _ ≤ ∏ l ∈ large, (sumResidues N l).card^(k+1) := by
      apply Finset.prod_le_prod'
      intro l hl
      obtain ⟨hlP, hlF⟩ := Finset.mem_filter.mp hl
      exact period_per_prime _ _ _ (hentry l hlP) (hP l hlP).pos
        (prime_card_lower N (hP l hlP)) (Nat.le_of_not_lt hlF)
    _ = (rows N large)^(k+1) := by simp [rows, Finset.prod_pow]
  have hrows : rows N large ≤ rows N P := by
    apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
    exact fun l hl _ => hentry l hl
  rw [← split, mul_pow]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hsmall _)
    (hlarge.trans (Nat.pow_le_pow_left hrows _))

/-- Rejecting even one entire interval forces a large fully tabulated group. -/
theorem rejecting_requires_rows {N lo width : ℕ} (k : ℕ) (P : Finset ℕ)
    (hP : ∀ l ∈ P, l.Prime) (rejected : ¬ passes N lo width P) :
    width^k ≤ ((3^(k+1))^(3^(k+1)))^k * (rows N P)^(k+1) := by
  have hper : width ≤ period P := by
    by_contra! h
    exact rejected (passes_of_period_le (fun l hl => (hP l hl).pos) h.le)
  exact (Nat.pow_le_pow_left hper _).trans (period_pow_le_rows N k P hP)

/-- On the part of the factor curve with x*y ≥ 2*N, the sum determines the
larger factor to within twice the error in the sum. -/
theorem large_factor_error {N x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : 2*N ≤ x*y) :
    |x-y| ≤ 2 * |(x + N/x) - (y + N/y)| := by
  have hid : (x + N/x) - (y + N/y) = (x-y) * (1 - N/(x*y)) := by
    field_simp
    ring
  have hc : 1/2 ≤ 1 - N/(x*y) := by
    have hn : N/(x*y) ≤ 1/2 := (div_le_iff₀ (mul_pos hx hy)).mpr (by linarith)
    linarith
  rw [hid, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - N/(x*y))]
  nlinarith [mul_nonneg (abs_nonneg (x-y)) (sub_nonneg.mpr hc)]

end FactorSumSieve
