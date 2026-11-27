import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.Ring

/-!
# Approximating a factor from the ratio of two factors

For positive factors `p ≤ q`, put `N = p*q`. A guess `r ≥ 1` for `q/p`
gives the estimate `√(N*r)` for `q`. The first public theorem bounds the
error in that estimate. The second partitions the resulting integer interval.
The last theorem bounds how many candidate values of `q` a fixed finite
collection of guesses can cover at a given precision.

## Application to integer factorization

Let b be the binary length of N = p*q, with p ≤ q prime. Fix an integer c ≥ 0.
Suppose a deterministic procedure given N produces polynomially many guesses
r ≥ 1 in polynomial time in b. At least one guess must approximate q/p to
within b^c / N^(1/4). Assume each guess is a rational of polynomial bit length
or that √(N*r) can be computed to absolute error one in polynomial time.
One center for q then has absolute error at most 1 + b^c N^(1/4)/2.
For the single fixed ratio r = √2, the center is the fourth root of 2*N².
Its floor is computable using two binary integer square roots.

Partition the interval around each center into O(1+b^c) integer blocks of
length max(1, floor(N^(1/4)/8)). For a block starting at A, the unknown
offset x = q-A satisfies A+x = 0 modulo q. Here q ≥ √N. The univariate
hidden-divisor theorem finds all such small offsets in polynomial time.
In its version with radius N^(1/4-ε)/2 and running time polynomial in both
b and 1/ε, take ε = 1/b. Since N < 2^b, its radius exceeds N^(1/4)/4.
Check candidate divisors by division. Finitely many small inputs can be
handled directly. The lattice theorem is an external published result.

For X ≤ p ≤ q ≤ 2X the ratio tolerance is O(X^(-1/2) (log X)^c).
For each fixed p, the finite bound allows each guess to cover at most
O(1 + X^(1/2) (log X)^c) integers q. The prime number theorem gives
Θ(X²/(log X)²) unordered pairs of distinct primes in this range. Summing
the bound over the possible primes p shows that any fixed list of size
polynomial in log X covers a proportion tending to zero. The same holds
for a list chosen only by input bit length, since this range of N has at
most three such lengths. This asymptotic deduction uses the prime number
theorem externally.

The counting bound uses the same list of guesses for every q being counted.
Producing sufficiently accurate guesses from each individual N is the
unproved step even for a semiprime with comparable prime factors.

## Sources

* D. Coppersmith (1996), https://doi.org/10.1007/3-540-68339-9_16
* The univariate hidden-divisor version of the theorem is stated at
  https://crypto.stanford.edu/cs355/20sp/hw2.pdf (Problem 2).
* B. de Weger, Cryptanalysis of RSA with Small Prime Difference (2002),
  https://doi.org/10.1007/s002000100088
* R. Erra and C. Grenier, The Fermat factorization method revisited,
  https://eprint.iacr.org/2009/318
* M. Hittmeir, Integer factorization as subset-sum problem,
  https://arxiv.org/abs/2205.10074
* S. Blake, Rational Base Descent, https://arxiv.org/abs/2605.08846
* Y. Gao, Y. Feng, H. Hu and Y. Pan, On Factoring and Power Divisor
  Problems via Rank-3 Lattices and the Second Vector, https://arxiv.org/abs/2512.19076
* P. Stănică, Improved deterministic integer factorization by quadratic-image
  sieving, https://arxiv.org/abs/2611.06580
-/

namespace FactorRatioBounds

private theorem sqrt_difference {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    2 * |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
  have sx : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have sy : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  have sum_nonneg : 0 ≤ Real.sqrt x + Real.sqrt y := by linarith
  have squares : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y by linarith)]
  calc
    2 * |Real.sqrt x - Real.sqrt y| ≤
        (Real.sqrt x + Real.sqrt y) * |Real.sqrt x - Real.sqrt y| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = |x - y| := by
      rw [← squares, abs_mul, abs_of_nonneg sum_nonneg, mul_comm]

/-- The larger factor is close to the computable center √(Nr) when r is
close to q/p. This inequality holds for all positive real factors. -/
theorem factor_error_of_ratio {p q r : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hr : 1 ≤ r) :
    2 * |q - Real.sqrt ((p*q)*r)| ≤ Real.sqrt (p*q) * |q/p - r| := by
  have hq : 0 ≤ q := by linarith
  have hn : 0 ≤ p*q := mul_nonneg hp.le hq
  have ratio : 1 ≤ q/p := (le_div_iff₀ hp).mpr (by simpa using hpq)
  have square : (p*q)*(q/p) = q^2 := by field_simp
  have exact_center : Real.sqrt (p*q) * Real.sqrt (q/p) = q := by
    rw [← Real.sqrt_mul hn, square, Real.sqrt_sq hq]
  calc
    2 * |q - Real.sqrt ((p*q)*r)| =
        2 * |Real.sqrt (p*q) * (Real.sqrt (q/p) - Real.sqrt r)| := by
      rw [mul_sub, exact_center, Real.sqrt_mul hn r]
    _ = Real.sqrt (p*q) * (2 * |Real.sqrt (q/p) - Real.sqrt r|) := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      ring
    _ ≤ Real.sqrt (p*q) * |q/p - r| :=
      mul_le_mul_of_nonneg_left (sqrt_difference ratio hr) (Real.sqrt_nonneg _)

/-- Every integer in [a, a+W] occurs in one of at most W/h + 1 blocks.
Its offset from the start of its block is strictly smaller than h. -/
theorem block_cover (q a W h : ℕ) (hh : 0 < h) (lo : a ≤ q) (hi : q ≤ a + W) :
    ∃ j ≤ W / h, ∃ e < h, q = a + j*h + e := by
  have span : q - a ≤ W := by omega
  refine ⟨(q-a)/h, Nat.div_le_div_right span, (q-a)%h, Nat.mod_lt _ hh, ?_⟩
  have decomp := Nat.div_add_mod (q-a) h
  rw [Nat.mul_comm h] at decomp
  omega

/-- For fixed p and one ratio guess, the possible integer values of q lie
in an interval of width at most 2*δ*p. -/
theorem one_ratio_capacity (p W : ℕ) (hp : 0 < p) (r δ : ℝ)
    (width : 2 * δ * (p : ℝ) ≤ W) (Q : Finset ℕ)
    (hits : ∀ q ∈ Q, |(q : ℝ) / p - r| ≤ δ) :
    Q.card ≤ W + 1 := by
  classical
  by_cases ne : Q.Nonempty
  · let a := Q.min' ne
    have ha : a ∈ Q := Q.min'_mem ne
    have pos : 0 < (p : ℝ) := by exact_mod_cast hp
    have contains : Q ⊆ Finset.Icc a (a + W) := by
      intro q hq
      have hi := (abs_le.mp (hits q hq)).2
      have lo := (abs_le.mp (hits a ha)).1
      have separated : ((q : ℝ) - a) / p ≤ 2 * δ := by rw [sub_div]; linarith
      have span := (div_le_iff₀ pos).mp separated
      have le_real : (q : ℝ) ≤ a + (W : ℝ) := by linarith
      exact Finset.mem_Icc.mpr ⟨Q.min'_le _ hq, by exact_mod_cast le_real⟩
    calc
      Q.card ≤ (Finset.Icc a (a + W)).card := Finset.card_le_card contains
      _ = W + 1 := by rw [Nat.card_Icc]; omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

/-- A list of R distinct guesses covers at most R*(W+1) candidate integers
for q whenever 2*δ*p ≤ W and all guesses use the same error tolerance δ. -/
theorem ratio_list_capacity (p W : ℕ) (hp : 0 < p) (δ : ℝ)
    (width : 2 * δ * (p : ℝ) ≤ W) (guesses : Finset ℝ) (Q : Finset ℕ)
    (cover : ∀ q ∈ Q, ∃ r ∈ guesses, |(q : ℝ) / p - r| ≤ δ) :
    Q.card ≤ guesses.card * (W + 1) := by
  classical
  let bucket (r : ℝ) : Finset ℕ := Q.filter fun (q : ℕ) => |(q : ℝ) / p - r| ≤ δ
  have covered : Q ⊆ guesses.biUnion bucket := by
    intro q hq
    obtain ⟨r, member, near⟩ := cover q hq
    exact Finset.mem_biUnion.mpr ⟨r, member, Finset.mem_filter.mpr ⟨hq, near⟩⟩
  apply (Finset.card_le_card covered).trans
  apply Finset.card_biUnion_le_card_mul
  intro r _
  exact one_ratio_capacity p W hp r δ width (bucket r)
    (fun _ h => (Finset.mem_filter.mp h).2)

/-- An example using only N and the fixed guess √2. The larger factor is
one above the integer fourth root of 2*N². -/
example :
    let n : ℕ := 141629071
    let a := (2 * n^2).sqrt.sqrt
    a = 14152 ∧ (a + 1) ∣ n ∧ n / (a + 1) = 10007 := by norm_num

end FactorRatioBounds

#print axioms FactorRatioBounds.factor_error_of_ratio
#print axioms FactorRatioBounds.block_cover
#print axioms FactorRatioBounds.ratio_list_capacity
