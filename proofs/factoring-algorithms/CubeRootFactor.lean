import Std

/-!
# Deterministic cube-root factor search

An integer-only variant of R. Sherman Lehman's multiplier method (1974).
Small trial divisors and nearby squares of multiples together cover every
composite integer. The pigeonhole argument is used only in the completeness
proof. The executable gets its candidates from the input integer alone.

`factorInteger_correct` proves the output specification for integer inputs.
`run_spec` bounds the total number of candidates across all recursive calls.
One probe is one trial divisor or one nearby-square candidate. Arithmetic
inside a probe, including a binary square root or a gcd, takes additional
work. `exceeds_every_polynomial` proves that, for this program, the probe
count alone exceeds any polynomial in the binary input length on some
arbitrarily large prime squares.

Checked with Lean 4.19.0 and its standard library. Run
`lean -DwarningAsError=true CubeRootFactor.lean` to check the file.
Evaluate `#eval CubeRootFactor.factorInteger 360` to obtain `[2, 2, 2, 3, 3, 5]`.
-/

namespace CubeRootFactor

/-- A natural number at least two whose only divisors are one and itself. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Product of the returned prime factors, including multiplicity. -/
def product : List Nat → Nat
  | [] => 1
  | x :: xs => x * product xs

private theorem product_append (xs ys : List Nat) :
    product (xs ++ ys) = product xs * product ys := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih => simp [product, ih, Nat.mul_assoc]

private theorem composite_pair {n : Nat} (hn : 2 ≤ n) (composite : ¬ Prime n) :
    ∃ p q, 2 ≤ p ∧ p ≤ q ∧ p < n ∧ p * q = n := by
  have proper : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
    apply Classical.byContradiction
    intro none
    apply composite
    refine ⟨hn, fun d dvd => ?_⟩
    by_cases one : d = 1
    · exact Or.inl one
    · apply Or.inr
      apply Classical.byContradiction
      exact fun ne => none ⟨d, dvd, one, ne⟩
  obtain ⟨d, ⟨q, eq⟩, notOne, notN⟩ := proper
  have d2 : 2 ≤ d := by
    by_cases zero : d = 0
    · simp [zero] at eq
      omega
    · omega
  have q2 : 2 ≤ q := by
    by_cases zero : q = 0
    · simp [zero] at eq
      omega
    · by_cases one : q = 1
      · simp [one] at eq
        omega
      · omega
  have dl : d < n := by have := Nat.mul_le_mul_left d q2; omega
  have ql : q < n := by have := Nat.mul_le_mul_right q d2; omega
  rcases Nat.le_total d q with order | order
  · exact ⟨d, q, d2, order, dl, eq.symm⟩
  · exact ⟨q, d, q2, order, ql, (Nat.mul_comm _ _).trans eq.symm⟩

local macro "factor_arith" : tactic =>
  `(tactic| (simp +arith [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
             Nat.mul_left_comm, Nat.mul_comm] <;> first | omega | ac_rfl))

/-- A successful split carries its divisibility and properness proofs. -/
structure Split (n : Nat) where
  divisor : Nat
  two_le : 2 ≤ divisor
  proper : divisor < n
  divides : divisor ∣ n

private def checked (n d : Nat) : Option (Split n) :=
  if h : 2 ≤ d ∧ d < n ∧ d ∣ n then some ⟨d, h.1, h.2.1, h.2.2⟩ else none

private theorem checked_hit {n d : Nat} (h : 2 ≤ d ∧ d < n ∧ d ∣ n) :
    checked n d ≠ none := by simp [checked, h]

/-- The search result and the number of candidates actually visited. -/
structure Search (α : Type) where
  answer : Option α
  probes : Nat

/-- Tail-recursive scan. `used` accounts for work before this interval. -/
private def scan {α : Type} (f : Nat → Search α) : Nat → Nat → Nat → Search α
  | _, 0, used => ⟨none, used⟩
  | lo, len + 1, used =>
    let r := f lo
    match r.answer with
    | some a => ⟨some a, used + r.probes⟩
    | none => scan f (lo + 1) len (used + r.probes)

private theorem scan_missed {α : Type} (f : Nat → Search α) (lo len used : Nat)
    (miss : (scan f lo len used).answer = none) (i : Nat) (low : lo ≤ i) (high : i < lo + len) :
    (f i).answer = none := by
  induction len generalizing lo used with
  | zero => omega
  | succ len ih =>
    cases atLo : (f lo).answer with
    | some a => simp [scan, atLo] at miss
    | none =>
      by_cases eq : i = lo
      · simpa only [eq] using atLo
      · apply ih (lo + 1) (used + (f lo).probes) _ (by omega) (by omega)
        simpa only [scan, atLo] using miss

private theorem scan_bound {α : Type} (f : Nat → Search α) (lo len used cap : Nat)
    (bound : ∀ i, lo ≤ i → i < lo + len → (f i).probes ≤ cap) :
    (scan f lo len used).probes ≤ used + len * cap := by
  induction len generalizing lo used with
  | zero => simp [scan]
  | succ len ih =>
    have first := bound lo (Nat.le_refl _) (by omega)
    have tail := ih (lo + 1) (used + (f lo).probes) (fun i low high => bound i (by omega) (by omega))
    cases h : (f lo).answer <;> simp only [scan, h, Nat.succ_mul] <;> omega

/-- `scale n` is the largest power of two whose sixth power is at most `n`
for positive `n`. The small-divisor cutoff is twice its square. -/
def scale (n : Nat) : Nat := 2 ^ (n.log2 / 6)

private theorem div_mono {a b k : Nat} (pos : 0 < k) (le : a ≤ b) : a / k ≤ b / k :=
  (Nat.le_div_iff_mul_le pos).2 (Nat.le_trans (Nat.div_mul_le_self a k) le)

private theorem scale_bounds {n : Nat} (hn : 0 < n) :
    (scale n)^6 ≤ n ∧ n < 64 * (scale n)^6 := by
  have lo := Nat.div_mul_le_self n.log2 6
  have hi : n.log2 + 1 ≤ n.log2 / 6 * 6 + 6 := by omega
  rw [scale, ← Nat.pow_mul]
  refine ⟨Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) lo) (Nat.log2_self_le (Nat.ne_of_gt hn)), ?_⟩
  calc
    n < 2^(n.log2 + 1) := Nat.lt_log2_self
    _ ≤ 2^(n.log2 / 6 * 6 + 6) := Nat.pow_le_pow_right (by decide) hi
    _ = 64 * 2^(n.log2 / 6 * 6) := by rw [Nat.pow_add, Nat.mul_comm]

private theorem square_le {x y : Nat} (h : x ≤ y) : x*x ≤ y*y :=
  Nat.mul_le_mul h h

private theorem square_lt {x y : Nat} (h : x < y) : x*x < y*y :=
  Nat.mul_lt_mul_of_lt_of_le h (Nat.le_of_lt h) (by omega)

private theorem le_of_square_le {x y : Nat} (h : x*x ≤ y*y) : x ≤ y := by
  apply Nat.le_of_not_gt
  intro no
  exact (Nat.not_lt_of_ge h) (square_lt no)

private theorem le_square {x : Nat} (h : 1 ≤ x) : x ≤ x*x := by
  simpa using Nat.mul_le_mul_left x h

/-- Decide one binary digit of the square root per recursive round. -/
def rootBits (n lo : Nat) : Nat → Nat
  | 0 => lo
  | k+1 =>
    let mid := lo + (1 <<< k)
    rootBits n (if mid*mid ≤ n then mid else lo) k

private theorem rootBits_bounds (n k lo : Nat) (lower : lo*lo ≤ n)
    (upper : n < (lo+2^k)*(lo+2^k)) :
    let r := rootBits n lo k
    r*r ≤ n ∧ n < (r+1)*(r+1) := by
  induction k generalizing lo with
  | zero => simpa [rootBits] using And.intro lower upper
  | succ k ih =>
    let mid := lo+2^k
    have width : lo+2^(k+1) = mid+2^k := by
      dsimp [mid]
      rw [Nat.pow_succ]
      omega
    rw [width] at upper
    by_cases up : mid*mid ≤ n
    · simpa only [rootBits, Nat.one_shiftLeft, if_pos up, mid] using ih mid up upper
    · simpa only [rootBits, Nat.one_shiftLeft, if_neg up, mid] using ih lo lower (by omega : n < mid*mid)

def floorRoot (n : Nat) : Nat := rootBits n 0 (n.log2+1)

theorem floorRoot_bounds (n : Nat) :
    (floorRoot n)*(floorRoot n) ≤ n ∧ n < (floorRoot n+1)*(floorRoot n+1) := by
  have big := Nat.lt_log2_self (n := n)
  have pos := Nat.two_pow_pos (n.log2+1)
  have upper := Nat.lt_of_lt_of_le big (le_square (by omega : 1 ≤ 2^(n.log2+1)))
  exact rootBits_bounds n (n.log2+1) 0 (by simp) (by simpa using upper)

theorem floorRoot_square (x : Nat) : floorRoot (x*x) = x := by
  obtain ⟨lo, hi⟩ := floorRoot_bounds (x*x)
  have one := le_of_square_le lo
  have two : x < floorRoot (x*x)+1 := by
    apply Nat.lt_of_not_ge
    intro no
    exact (Nat.not_le_of_gt hi) (square_le no)
  omega


private theorem root_sq (n : Nat) : floorRoot (n^2) = n := by
  simpa [Nat.pow_two] using floorRoot_square n

private theorem le_root {i n : Nat} (square : i*i ≤ n) : i ≤ floorRoot n := by
  apply Nat.le_of_not_gt
  intro smaller
  have wrong := square_le (show floorRoot n + 1 ≤ i by omega)
  have upper := (floorRoot_bounds n).2
  omega

private theorem root_lt {i n : Nat} (square : n < i*i) : floorRoot n < i := by
  apply Nat.lt_of_not_ge
  intro smaller
  have wrong := square_le smaller
  have lower := (floorRoot_bounds n).1
  omega

/-- A map from the first m+1 indices into m buckets has a repeated value. -/
private theorem same_bucket (m : Nat) (f : Nat → Nat) (h : ∀ i, i ≤ m → f i < m) :
    ∃ i j, i < j ∧ j ≤ m ∧ f i = f j := by
  induction m generalizing f with
  | zero => have wrong := h 0 (by omega); omega
  | succ m ih =>
    by_cases pair : ∃ i, i < m+1 ∧ f i = f (m+1)
    · obtain ⟨i, hi, eq⟩ := pair
      exact ⟨i, m+1, hi, Nat.le_refl _, eq⟩
    · let x := f (m+1)
      let g i := if f i < x then f i else f i - 1
      have noEq (i) (hi : i ≤ m) : f i ≠ x := fun eq => pair ⟨i, by omega, eq⟩
      have xmax : x ≤ m := by have := h (m+1) (by omega); dsimp [x]; omega
      have gr (i) (hi : i ≤ m) : g i < m := by
        have fi := h i (by omega)
        have ne := noEq i hi
        dsimp [g]
        split <;> omega
      obtain ⟨i, j, ij, jm, geq⟩ := ih g gr
      refine ⟨i, j, ij, by omega, ?_⟩
      have neqI := noEq i (by omega)
      have neqJ := noEq j jm
      by_cases li : f i < x <;> by_cases lj : f j < x <;> simp [g, li, lj] at geq <;> omega

/-- On the candidate `x`, test `x² - 4kn` for being a square and check the
resulting gcd. `checked` validates every returned divisor. -/
private def squareTest (n k x : Nat) : Option (Split n) :=
  let m := 4 * k * n
  let delta := x^2 - m
  let y := floorRoot delta
  if m ≤ x^2 ∧ y^2 = delta then checked n (((x + y) / 2).gcd n) else none

private def offsets (n t j k : Nat) : Search (Split n) :=
  let center := floorRoot (4 * k * n)
  scan (fun i => ⟨squareTest n k (center + i), 1⟩) 0 (4 * t / j + 2) 0

private def block (n t j : Nat) : Search (Split n) :=
  scan (fun u => offsets n t j (j^2 + u)) 0 (2 * j + 1) 0

private def smallSearch (n t : Nat) : Search (Split n) :=
  scan (fun d => ⟨checked n d, 1⟩) 2 (2 * t^2 - 1) 0

/-- Try small divisors first, then square differences for multiples of the input. -/
def findSplit (n : Nat) : Search (Split n) :=
  let t := scale n
  let small := smallSearch n t
  match small.answer with
  | some _ => small
  | none => scan (block n t) 1 (10 * t) small.probes

/-! ## Coverage by multiples with nearby factors -/

private structure Near (p q h a b : Nat) : Prop where
  a_pos : 0 < a
  b_pos : 0 < b
  a_lt : a < q
  b_lt : b < p
  left_close : a * p < b * q + h
  right_close : b * q < a * p + h
  a_bound : h * a ≤ 3 * q
  b_bound : h * b ≤ 2 * p

/-- Two multiples of `q` have remainders modulo `p` in the same bucket of
width `h`. Subtracting their quotient/remainder identities gives `a,b`. -/
private theorem near_multipliers {p q h : Nat} (h2 : 2 ≤ h) (small : h < p) (order : p ≤ q) :
    ∃ a b, Near p q h a b := by
  let m := p / h + 1
  let bucket (i : Nat) := (i * q % p) / h
  obtain ⟨i, j, ij, jm, sameBucket⟩ := same_bucket m bucket
    (fun i _ => Nat.lt_succ_of_le (div_mono (by omega : 0 < h)
      (Nat.le_of_lt (Nat.mod_lt (i * q) (by omega : 0 < p)))))
  let b := j - i
  let s := (i * q) / p
  let t := (j * q) / p
  let a := t - s
  let ri := i * q % p
  let rj := j * q % p
  have pp : 0 < p := by omega
  have inc : i * q + p ≤ j * q := by
    calc
      i * q + p ≤ i * q + q := Nat.add_le_add_left order _
      _ = (i + 1) * q := (Nat.succ_mul i q).symm
      _ ≤ j * q := Nat.mul_le_mul_right q ij
  have st : s + 1 ≤ t := by
    apply (Nat.le_div_iff_mul_le pp).2
    rw [Nat.succ_mul]
    exact Nat.le_trans (Nat.add_le_add_right (Nat.div_mul_le_self (i * q) p) p) inc
  have ea : a * p + s * p = t * p := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : s ≤ t)]
  have eb : b * q + i * q = j * q := by rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt ij)]
  have esi : ri + s * p = i * q := by simpa only [Nat.mul_comm p] using Nat.mod_add_div (i*q) p
  have etj : rj + t * p = j * q := by simpa only [Nat.mul_comm p] using Nat.mod_add_div (j*q) p
  have balance : a * p + rj = b * q + ri := by omega
  change ri / h = rj / h at sameBucket
  have hri := Nat.mod_add_div ri h
  have hrj := Nat.mod_add_div rj h
  rw [← sameBucket] at hrj
  have riSmall := Nat.mod_lt ri (by omega : 0 < h)
  have rjSmall := Nat.mod_lt rj (by omega : 0 < h)
  have close₁ : a * p < b * q + h := by omega
  have close₂ : b * q < a * p + h := by omega
  have bmax : b ≤ p / h + 1 := by dsimp [b]; exact Nat.le_trans (Nat.sub_le _ _) jm
  have below : b < p := by have := Nat.div_le_div_left (a := p) h2 (by decide); omega
  have above : a < q := by
    apply Nat.lt_of_mul_lt_mul_right (a := p)
    calc
      a * p < b * q + h := close₁
      _ ≤ b * q + q := by omega
      _ = (b + 1) * q := (Nat.succ_mul _ _).symm
      _ ≤ p * q := Nat.mul_le_mul_right q below
      _ = q * p := Nat.mul_comm _ _
  have hb : h * b ≤ 2 * p := by
    have bound := Nat.mul_le_mul_left h bmax
    rw [Nat.mul_succ] at bound
    have := Nat.mul_div_le p h
    omega
  have ha : h * a ≤ 3 * q := by
    apply Nat.le_of_mul_le_mul_right (c := p) _ pp
    calc
      (h * a) * p ≤ h * (b * q + h) := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_of_lt close₁)
      _ = (h * b) * q + h * h := by factor_arith
      _ ≤ (2 * p) * q + p * q := Nat.add_le_add (Nat.mul_le_mul_right q hb) (Nat.mul_le_mul (Nat.le_of_lt small) (by omega))
      _ = (3 * q) * p := by rw [Nat.mul_assoc 2, Nat.mul_assoc 3, Nat.mul_comm q p]; omega
  exact ⟨a, b, by dsimp [a]; omega, by dsimp [b]; omega, above, below, close₁, close₂, ha, hb⟩

private theorem difference_square {u v h : Nat} (c₁ : u < v + h) (c₂ : v < u + h) :
    ∃ y < h, (u + v)^2 = 4 * u * v + y^2 ∧ (u + v + y) / 2 = max u v := by
  rcases Nat.le_total u v with uv | vu
  · refine ⟨v - u, by omega, ?_, by rw [Nat.max_eq_right uv]; omega⟩
    obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le uv
    rw [Nat.add_sub_cancel_left]; factor_arith
  · refine ⟨u - v, by omega, ?_, by rw [Nat.max_eq_left vu]; omega⟩
    obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le vu
    rw [Nat.add_sub_cancel_left]; factor_arith

private theorem gcd_hit {n z m : Nat} (hm : 2 ≤ m) (mz : m ∣ z) (mn : m ∣ n)
    (pos : 0 < z) (proper : z < n) : checked n (z.gcd n) ≠ none := by
  apply checked_hit
  exact ⟨Nat.le_trans hm (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left n pos) (Nat.dvd_gcd mz mn)),
    Nat.lt_of_le_of_lt (Nat.gcd_le_left _ pos) proper, Nat.gcd_dvd_right _ _⟩

private theorem square_hit {n k x y : Nat} (difference : x^2 = 4 * k * n + y^2)
    (hit : checked n (((x + y) / 2).gcd n) ≠ none) : squareTest n k x ≠ none := by
  have delta : x^2 - 4 * k * n = y^2 := by omega
  have lo : 4 * k * n ≤ x^2 := by omega
  simpa [squareTest, delta, root_sq, lo] using hit

/-- `j` groups the multipliers by the integer square root of `k`. The width
of the search around the square root shrinks as `j` grows. -/
private theorem square_window {n t k j x y : Nat} (tp : 0 < t) (jp : 0 < j)
    (size : t^6 ≤ n) (jl : j * j ≤ k) (near : y < 2 * t^2)
    (difference : x^2 = 4 * k * n + y^2) :
    floorRoot (4 * k * n) ≤ x ∧ x < (floorRoot (4 * k * n)) + (4 * t / j + 2) := by
  let r := floorRoot (4 * k * n)
  have square : x * x = 4 * k * n + y^2 := by simpa only [Nat.pow_two x] using difference
  have rl : r * r ≤ 4 * k * n := (floorRoot_bounds _).1
  have low : r ≤ x := le_of_square_le (by omega)
  refine ⟨low, ?_⟩
  change x < r + (4 * t / j + 2)
  by_cases past : r + 1 ≤ x
  · let e := x - (r + 1)
    have ex : e * x + (r + 1) * x = x * x := by rw [← Nat.add_mul, Nat.sub_add_cancel past]
    have next : 4 * k * n < (r + 1) * (r + 1) := (floorRoot_bounds _).2
    have cover := Nat.lt_of_lt_of_le next (Nat.mul_le_mul_left (r + 1) past)
    have small : e * x ≤ y^2 := by omega
    have jx : j * t^3 ≤ x := by
      apply le_of_square_le
      calc
        (j * t^3) * (j * t^3) = (j * j) * t^6 := by factor_arith
        _ ≤ k * n := Nat.mul_le_mul jl size
        _ ≤ x * x := by rw [Nat.mul_assoc 4 k n] at square; omega
    have bound : e * j ≤ 4 * t := by
      apply Nat.le_of_mul_le_mul_right (c := t^3) _ (Nat.pow_pos tp)
      calc
        (e * j) * t^3 = e * (j * t^3) := Nat.mul_assoc _ _ _
        _ ≤ e * x := Nat.mul_le_mul_left _ jx
        _ ≤ y^2 := small
        _ ≤ (2 * t^2)^2 := Nat.pow_le_pow_left (Nat.le_of_lt near) 2
        _ = (4 * t) * t^3 := by factor_arith
    have off := (Nat.le_div_iff_mul_le jp).2 bound
    change x - (r + 1) ≤ 4 * t / j at off
    have offPos := Nat.zero_le (4 * t / j)
    omega
  · have offPos := Nat.zero_le (4 * t / j)
    omega

private theorem missed_square {n t used j k x : Nat}
    (noneFound : (scan (block n t) 1 (10 * t) used).answer = none)
    (jpos : 1 ≤ j) (jmax : j ≤ 10 * t) (klo : j^2 ≤ k) (khi : k < (j + 1)^2)
    (xlo : floorRoot (4 * k * n) ≤ x) (xhi : x < (floorRoot (4 * k * n)) + (4 * t / j + 2)) :
    squareTest n k x = none := by
  have noneJ := scan_missed _ _ _ _ noneFound j jpos (by omega)
  have top : (j + 1)^2 = j^2 + 2 * j + 1 := by factor_arith
  have noneK := scan_missed _ _ _ _ noneJ (k - j^2) (Nat.zero_le _) (by omega)
  change (offsets n t j (j^2 + (k - j^2))).answer = none at noneK
  rw [Nat.add_sub_of_le klo] at noneK
  let r := floorRoot (4 * k * n)
  have noneX := scan_missed _ _ _ _ noneK (x - r) (Nat.zero_le _) (by dsimp [r]; omega)
  change squareTest n k (r + (x - r)) = none at noneX
  rwa [Nat.add_sub_of_le xlo] at noneX

/-- Every factor pair beyond the small-divisor cutoff produces a candidate
visited by the multiplier loop. No primality promise about the pair is used. -/
private theorem large_hit {p q t : Nat} (tp : 0 < t) (lo : t^6 ≤ p * q) (hi : p * q < 64 * t^6)
    (small : 2 * t^2 < p) (order : p ≤ q) (used : Nat) :
    (scan (block (p * q) t) 1 (10 * t) used).answer ≠ none := by
  intro miss
  have t2 : 0 < t^2 := Nat.pow_pos tp
  have pp : 0 < p := by omega
  have qp : 0 < q := by omega
  obtain ⟨a, b, near⟩ := near_multipliers (by omega : 2 ≤ 2 * t^2) small order
  let k := a * b
  let x := a * p + b * q
  let j := floorRoot k
  have kLim : k < 96 * t^2 := by
    apply Nat.lt_of_mul_lt_mul_right (a := 4 * t^4)
    calc
      k * (4 * t^4) = ((2 * t^2) * a) * ((2 * t^2) * b) := by dsimp [k]; factor_arith
      _ ≤ (3 * q) * (2 * p) := Nat.mul_le_mul near.a_bound near.b_bound
      _ = 6 * (p * q) := by factor_arith
      _ < 6 * (64 * t^6) := Nat.mul_lt_mul_of_pos_left hi (by decide)
      _ = (96 * t^2) * (4 * t^4) := by factor_arith
  have jp : 1 ≤ j := le_root (Nat.mul_pos near.a_pos near.b_pos)
  have jmax : j < 10 * t := by
    apply root_lt
    calc
      k < 96 * t^2 := kLim
      _ ≤ 100 * t^2 := Nat.mul_le_mul_right _ (by decide)
      _ = (10 * t) * (10 * t) := by factor_arith
  obtain ⟨y, ylo, sq, half⟩ := difference_square near.left_close near.right_close
  have diff : x^2 = 4 * k * (p * q) + y^2 := sq.trans (by dsimp [k]; factor_arith)
  obtain ⟨xlo, xhi⟩ := square_window tp jp lo (floorRoot_bounds k).1 ylo diff
  have fail := missed_square miss jp (Nat.le_of_lt jmax) (by simpa only [Nat.pow_two] using (floorRoot_bounds k).1)
    (by simpa only [Nat.pow_two] using (floorRoot_bounds k).2) xlo xhi
  apply square_hit diff _ fail
  change checked (p * q) (((a * p + b * q + y) / 2).gcd (p * q)) ≠ none
  rw [half]
  rcases Nat.le_total (a * p) (b * q) with left | right
  · rw [Nat.max_eq_right left]
    exact gcd_hit (m := q) (by omega) (Nat.dvd_mul_left q b) (Nat.dvd_mul_left q p)
      (Nat.mul_pos near.b_pos qp) (Nat.mul_lt_mul_of_pos_right near.b_lt qp)
  · rw [Nat.max_eq_left right]
    exact gcd_hit (m := p) (by omega) (Nat.dvd_mul_left p a) (Nat.dvd_mul_right p q)
      (Nat.mul_pos near.a_pos pp) (Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_right near.a_lt pp) (Nat.mul_comm q p))

private theorem no_split_of_prime {n : Nat} (hp : Prime n) (s : Option (Split n)) : s = none := by
  cases s with
  | none => rfl
  | some d =>
    have bound := d.proper
    have min := d.two_le
    rcases hp.2 d.divisor d.divides with h | h <;> omega

/-- Exhausting this executable search proves primality. -/
theorem findSplit_none_iff {n : Nat} (hn : 2 ≤ n) : (findSplit n).answer = none ↔ Prime n := by
  refine ⟨?_, fun prime => no_split_of_prime prime _⟩
  intro miss
  apply Classical.byContradiction
  intro composite
  let t := scale n
  let early := smallSearch n t
  change (match early.answer with
    | some _ => early
    | none => scan (block n t) 1 (10 * t) early.probes).answer = none at miss
  cases smallResult : early.answer with
  | some d => simp [smallResult] at miss
  | none =>
    simp only [smallResult] at miss
    obtain ⟨p, q, pp, ord, proper, eq⟩ := composite_pair hn composite
    have dvd : p ∣ n := ⟨q, eq.symm⟩
    have cutoff : 2 * t^2 < p := by
      apply Nat.lt_of_not_ge
      intro tooSmall
      exact checked_hit ⟨pp, proper, dvd⟩ (scan_missed _ _ _ _ smallResult p pp (by omega))
    have size := scale_bounds (n := n) (by omega)
    have fail := large_hit (t := t) (Nat.two_pow_pos _) (by rw [eq]; exact size.1)
      (by rw [eq]; exact size.2) cutoff ord early.probes
    rw [eq] at fail
    exact fail miss

/-! ## Candidate counts and complete factorization -/

private theorem small_bound (n t : Nat) : (smallSearch n t).probes ≤ 2 * t^2 - 1 := by
  simpa [smallSearch] using scan_bound (fun d => (⟨checked n d, 1⟩ : Search _))
    2 (2 * t^2 - 1) 0 1 (by intros; exact Nat.le_refl _)

private theorem offsets_bound (n t j k : Nat) : (offsets n t j k).probes ≤ 4 * t / j + 2 := by
  unfold offsets
  simpa using scan_bound (fun i => (⟨squareTest n k ((floorRoot (4 * k * n)) + i), 1⟩ : Search _))
    0 (4 * t / j + 2) 0 1 (by intros; exact Nat.le_refl _)

private theorem block_bound (n t j : Nat) (positive : 1 ≤ j) (maxJ : j ≤ 10 * t) :
    (block n t j).probes ≤ 72 * t := by
  have search := scan_bound (fun u => offsets n t j (j^2 + u)) 0 (2 * j + 1) 0
    (4 * t / j + 2) (fun _ _ _ => offsets_bound _ _ _ _)
  calc
    (block n t j).probes ≤ (2 * j + 1) * (4 * t / j + 2) := by simpa [block] using search
    _ ≤ (3 * j) * (4 * t / j + 2) := Nat.mul_le_mul_right _ (by omega)
    _ = 3 * (j * (4 * t / j)) + 6 * j := by
      generalize 4 * t / j = w
      rw [Nat.mul_add, Nat.mul_assoc 3 j w]
      have eq : (3*j)*2 = 6*j := by factor_arith
      rw [eq]
    _ ≤ 72 * t := by have := Nat.mul_div_le (4 * t) j; omega

/-- All-input upper bound on divisor and nearby-square candidates in one split. -/
theorem findSplit_bound (n : Nat) : (findSplit n).probes ≤ 722 * (scale n)^2 := by
  let t := scale n
  let early := smallSearch n t
  have first := small_bound n t
  change early.probes ≤ _ at first
  have second := scan_bound (block n t) 1 (10 * t) early.probes (72 * t)
    (fun j pos hi => block_bound n t j pos (by omega))
  have size : 10 * t * (72 * t) = 720 * t^2 := by factor_arith
  change (match early.answer with
    | some _ => early
    | none => scan (block n t) 1 (10 * t) early.probes).probes ≤ 722 * t^2
  cases early.answer <;> dsimp only <;> omega

structure Result where
  factors : List Nat
  probes : Nat
  deriving Repr, DecidableEq

/-- Split and recurse on both strictly smaller cofactors. -/
def run (n : Nat) : Result :=
  if n < 2 then ⟨[], 0⟩ else
    let r := findSplit n
    match r.answer with
    | none => ⟨[n], r.probes⟩
    | some s =>
      let left := run s.divisor
      let right := run (n / s.divisor)
      ⟨left.factors ++ right.factors, r.probes + left.probes + right.probes⟩
termination_by n
decreasing_by
  · exact s.proper
  · exact Nat.div_lt_self (by omega) (by have := s.two_le; omega)

private theorem log_mono {a b : Nat} (ha : 0 < a) (le : a ≤ b) : a.log2 ≤ b.log2 :=
  (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le (Nat.ne_of_gt ha)) le)

private theorem scale_mono {a b : Nat} (ha : 0 < a) (le : a ≤ b) : scale a ≤ scale b :=
  Nat.pow_le_pow_right (by decide) (div_mono (by decide : 0 < 6) (log_mono ha le))

/-- Full factorization, including repeated prime powers, and a global budget
for all calls to the splitter. -/
theorem run_spec (n : Nat) (hn : 2 ≤ n) :
    product (run n).factors = n ∧ (∀ p ∈ (run n).factors, Prime p) ∧
    (run n).probes ≤ (2 * n.log2 - 1) * (722 * (scale n)^2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [run, if_neg (by omega)]
    dsimp only
    cases found : (findSplit n).answer with
    | none =>
      have prime := (findSplit_none_iff hn).mp found
      have pos : 1 ≤ n.log2 := (Nat.le_log2 (by omega)).2 (by simpa using hn)
      refine ⟨by simp [product], by simpa using prime, Nat.le_trans (findSplit_bound n) ?_⟩
      simpa using Nat.mul_le_mul_right (722 * (scale n)^2) (show 1 ≤ 2 * n.log2 - 1 by omega)
    | some s =>
      let d := s.divisor
      let q := n / d
      let cap := 722 * (scale n)^2
      have hd : 2 ≤ d := s.two_le
      have hp : d < n := s.proper
      have qp : q < n := Nat.div_lt_self (by omega) (by omega)
      have prod : d * q = n := by rw [Nat.mul_comm d]; exact Nat.div_mul_cancel s.divides
      have hq : 2 ≤ q := by
        apply Nat.le_of_not_gt
        intro tiny
        have nonnegative := Nat.zero_le q
        rcases (by omega : q = 0 ∨ q = 1) with eq | eq
        · rw [eq, Nat.mul_zero] at prod
          omega
        · rw [eq, Nat.mul_one] at prod
          omega
      obtain ⟨dp, dpr, dw⟩ := ih d hp hd
      obtain ⟨qp', qpr, qw⟩ := ih q qp hq
      refine ⟨?_, ?_, ?_⟩
      · change product ((run d).factors ++ (run q).factors) = n
        rw [product_append, dp, qp', prod]
      · intro p member
        exact (List.mem_append.mp member).elim (dpr p) (qpr p)
      · have ds := Nat.pow_le_pow_left (scale_mono (by omega : 0 < d) (Nat.le_of_lt hp)) 2
        have qs := Nat.pow_le_pow_left (scale_mono (by omega : 0 < q) (Nat.le_of_lt qp)) 2
        have dc : (run d).probes ≤ (2 * d.log2 - 1) * cap :=
          Nat.le_trans dw (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 722 ds))
        have qc : (run q).probes ≤ (2 * q.log2 - 1) * cap :=
          Nat.le_trans qw (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 722 qs))
        have dl : 1 ≤ d.log2 := (Nat.le_log2 (by omega)).2 (by simpa using hd)
        have ql : 1 ≤ q.log2 := (Nat.le_log2 (by omega)).2 (by simpa using hq)
        have sum : d.log2 + q.log2 ≤ n.log2 := by
          apply (Nat.le_log2 (by omega)).2
          rw [Nat.pow_add, ← prod]
          exact Nat.mul_le_mul (Nat.log2_self_le (by omega)) (Nat.log2_self_le (by omega))
        change (findSplit n).probes + (run d).probes + (run q).probes ≤ _ * cap
        calc
          _ ≤ cap + (2 * d.log2 - 1) * cap + (2 * q.log2 - 1) * cap :=
            Nat.add_le_add (Nat.add_le_add (findSplit_bound n) dc) qc
          _ = (1 + (2 * d.log2 - 1) + (2 * q.log2 - 1)) * cap := by simp only [Nat.add_mul, Nat.one_mul]
          _ ≤ (2 * n.log2 - 1) * cap := Nat.mul_le_mul_right _ (by omega)

/-- Integer input with positive natural primes as outputs. -/
def factorInteger (n : Int) : List Nat := (run n.toNat).factors

theorem factorInteger_correct (n : Int) (hn : 2 ≤ n) :
    (↑(product (factorInteger n)) : Int) = n ∧ ∀ p ∈ factorInteger n, Prime p := by
  obtain ⟨prod, prime, _⟩ := run_spec n.toNat (by omega)
  refine ⟨?_, prime⟩
  simpa only [factorInteger, prod] using Int.toNat_of_nonneg (by omega : 0 ≤ n)

private theorem scan_keeps_work {α : Type} (f : Nat → Search α) (lo len used : Nat) :
    used ≤ (scan f lo len used).probes := by
  induction len generalizing lo used with
  | zero => exact Nat.le_refl _
  | succ len ih =>
    have next := ih (lo + 1) (used + (f lo).probes)
    cases atLo : (f lo).answer <;> simp only [scan, atLo] <;> omega

private theorem empty_interval {α : Type} (f : Nat → Search α) (lo len used : Nat)
    (empty : ∀ i, lo ≤ i → i < lo + len → f i = ⟨none, 1⟩) :
    scan f lo len used = ⟨none, used + len⟩ := by
  induction len generalizing lo used with
  | zero => rfl
  | succ len ih =>
    rw [scan, empty lo (by omega) (by omega)]
    have tail := ih (lo + 1) (used + 1) (fun i l h => empty i (by omega) (by omega))
    simpa only [Nat.add_right_comm used 1 len, Nat.add_assoc] using tail

/-- Any input without a divisor up to the cutoff incurs the entire trial prefix. -/
theorem prefix_lower {n : Nat} (hn : 2 ≤ n)
    (rough : ∀ d, 2 ≤ d → d ≤ 2 * (scale n)^2 → ¬ d ∣ n) :
    2 * (scale n)^2 - 1 ≤ (run n).probes := by
  let t := scale n
  have tpos : 0 < t := Nat.two_pow_pos _
  have sqpos := Nat.pow_pos tpos (n := 2)
  have exhausted : smallSearch n t = ⟨none, 2 * t^2 - 1⟩ := by
    unfold smallSearch
    apply Eq.trans (empty_interval (fun d => (⟨checked n d, 1⟩ : Search (Split n)))
      2 (2 * t^2 - 1) 0 ?_) (by simp)
    intro d hd hi
    have miss := rough d hd (by change d ≤ 2 * t^2; omega)
    simp [checked, miss]
  have first : 2 * t^2 - 1 ≤ (findSplit n).probes := by
    unfold findSplit
    change _ ≤ (match (smallSearch n t).answer with
      | some _ => smallSearch n t
      | none => scan (block n t) 1 (10 * t) (smallSearch n t).probes).probes
    rw [exhausted]
    exact scan_keeps_work _ _ _ _
  change 2 * t^2 - 1 ≤ (run n).probes
  rw [run, if_neg (by omega)]
  dsimp only
  cases (findSplit n).answer <;> dsimp only <;> omega

/-- On `p*q` with `16 < p ≤ q ≤ 2p` prime, the prefix alone performs at least
`2 * 4^(floor(log₂(p*q)/6)) - 1` tests. This applies to distinct primes. -/
theorem balanced_lower {p q : Nat} (hp : Prime p) (hq : Prime q) (large : 16 < p)
    (order : p ≤ q) (close : q ≤ 2 * p) :
    2 * (scale (p * q))^2 - 1 ≤ (run (p * q)).probes := by
  let t := scale (p * q)
  have pp : 0 < p := by have := hp.1; omega
  have qp : 0 < q := by have := hq.1; omega
  have pos := Nat.mul_pos pp qp
  have small := (scale_bounds pos).1
  change t^6 ≤ p * q at small
  have cutoff : 2 * t^2 < p := by
    have upper : (2 * t^2)^3 < p^3 := by
      calc
        (2 * t^2)^3 = 8 * t^6 := by factor_arith
        _ ≤ 8 * (p * q) := Nat.mul_le_mul_left 8 small
        _ ≤ 8 * (p * (2 * p)) := Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left p close)
        _ = 16 * (p * p) := by factor_arith
        _ < p * (p * p) := Nat.mul_lt_mul_of_pos_right large (Nat.mul_pos pp pp)
        _ = p^3 := by factor_arith
    apply Nat.lt_of_not_ge
    intro opposite
    exact (Nat.not_le_of_gt upper) (Nat.pow_le_pow_left opposite 3)
  apply prefix_lower (by have := Nat.mul_le_mul hp.1 hq.1; omega)
  intro d hd limit dvd
  change d ≤ 2 * t^2 at limit
  obtain ⟨u, v, hu, hv, eq⟩ := Nat.dvd_mul.mp dvd
  have nBig : p ≤ p * q := by simpa using Nat.mul_le_mul_left p (show 1 ≤ q by omega)
  rcases hp.2 u hu with a | a <;> rcases hq.2 v hv with b | b <;>
    rw [a, b] at eq <;> (try simp only [Nat.one_mul, Nat.mul_one] at eq) <;> omega


/-! ## Lower bound in the binary input length -/

/-- The number of digits of the usual binary encoding, for positive inputs.
The encoding of zero has one digit. -/
def bitLength (n : Nat) : Nat := n.log2 + 1

private def factorial : Nat → Nat
  | 0 => 1
  | k+1 => (k+1) * factorial k

private theorem factorial_pos (k : Nat) : 0 < factorial k := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact Nat.mul_pos (by omega) ih

private theorem divides_factorial {d : Nat} (dp : 0 < d) (k : Nat) (bound : d ≤ k) :
    d ∣ factorial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eq : d = k+1
    · subst d
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left _ _)

/-- Apply Euclid's argument to a prime in our own factorization of k! + 1. -/
private theorem prime_above (k : Nat) : ∃ p, Prime p ∧ k < p := by
  let n := factorial k + 1
  have hn : 2 ≤ n := by have := factorial_pos k; dsimp [n]; omega
  obtain ⟨factorization, primes, _⟩ := run_spec n hn
  cases fs : (run n).factors with
  | nil => rw [fs] at factorization; change 1 = n at factorization; omega
  | cons p ps =>
    have hp := primes p (by simp [fs])
    have atLeastTwo := hp.1
    have dvd : p ∣ factorial k + 1 := by
      rw [fs] at factorization
      exact ⟨product ps, factorization.symm⟩
    refine ⟨p, hp, Nat.lt_of_not_ge ?_⟩
    intro small
    have one := (Nat.dvd_add_iff_right (divides_factorial (by omega : 0 < p) k small)).2 dvd
    have tooSmall := Nat.le_of_dvd (by decide : 0 < 1) one
    omega

private theorem square_le_pow_two (r : Nat) (hr : 4 ≤ r) : r * r ≤ 2^r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction k with
  | zero => decide
  | succ k ih =>
    let z := 4 + k
    have linear := Nat.mul_le_mul_right z (show 4 ≤ z by dsimp [z]; omega)
    have extra : z * 2 + 1 ≤ z * z := by dsimp [z] at *; omega
    have next : (z+1)*(z+1) = z*z + z*2 + 1 := by
      rw [Nat.succ_mul, Nat.mul_succ]
      omega
    change (z+1)*(z+1) ≤ 2^(z+1)
    rw [next, Nat.pow_succ]
    change z*z ≤ 2^z at ih
    omega

/-- For sufficiently large b, even 2^floor((b-1)/6) exceeds c*b^e. -/
private theorem exponential_dominates (c e b : Nat) (pos : 0 < b)
    (big : 6 * (c + e + 1) + 4 ≤ b.log2) : c * b^e < 2^((b-1)/6) := by
  let r := b.log2
  have hr : 6 * (c + e + 1) + 4 ≤ r := big
  have square := square_le_pow_two r (by omega)
  have rsize : 2^r ≤ b := Nat.log2_self_le (Nat.ne_of_gt pos)
  have linear : 6 * (c + (r+1)*e) + 1 ≤ r*r := by
    have mul := Nat.mul_le_mul_right r (show 6*e+1 ≤ r by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm e r] at mul
    rw [Nat.succ_mul r e]
    omega
  have exponent : c + (r+1)*e ≤ (b-1)/6 := by omega
  calc
    c * b^e < 2^c * (2^(r+1))^e :=
      Nat.mul_lt_mul_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_log2_self (n := b))) e)
        (Nat.pow_pos (Nat.two_pow_pos _))
    _ = 2^(c+(r+1)*e) := by rw [Nat.pow_add 2 c, Nat.pow_mul]
    _ ≤ 2^((b-1)/6) := Nat.pow_le_pow_right (by decide) exponent

/-- For every polynomial budget c*b^e and every minimum binary length,
some prime square of at least that length exceeds the budget in candidate
tests. This is an obstruction for this implementation. -/
theorem exceeds_every_polynomial (c e minimumBits : Nat) :
    ∃ p, Prime p ∧ minimumBits ≤ bitLength (p*p) ∧
      c * (bitLength (p*p))^e < (run (p*p)).probes := by
  let m := 6*(c+e+1) + 4 + minimumBits
  obtain ⟨p, prime, pl⟩ := prime_above (2^(2^m) + 17)
  have expPos := Nat.two_pow_pos (2^m)
  have pp : 0 < p := by omega
  have positive := Nat.mul_pos pp pp
  have ns := Nat.le_mul_of_pos_right p pp
  have large : 2^m ≤ (p*p).log2 :=
    (Nat.le_log2 (Nat.ne_of_gt positive)).2 (by omega)
  let b := bitLength (p*p)
  have bl : 2^m ≤ b := by dsimp [b, bitLength]; omega
  have bp : 0 < b := by dsimp [b, bitLength]; omega
  have ml : m ≤ b.log2 := (Nat.le_log2 (Nat.ne_of_gt bp)).2 bl
  have big : 6*(c+e+1)+4 ≤ b.log2 := by dsimp [m] at ml; omega
  have beats := exponential_dominates c e b bp big
  have equal : 2^((b-1)/6) = scale (p*p) := by simp [b, bitLength, scale]
  rw [equal] at beats
  have tests := balanced_lower prime prime (by omega) (Nat.le_refl _) (by omega)
  let t := scale (p*p)
  have tp : 0 < t := Nat.two_pow_pos _
  have t2 : t ≤ t^2 := by simpa [Nat.pow_two] using Nat.le_mul_of_pos_right t tp
  change c * b^e < t at beats
  change 2*t^2-1 ≤ (run (p*p)).probes at tests
  have mp := Nat.lt_two_pow_self (n := m)
  refine ⟨p, prime, ?_, ?_⟩
  · change minimumBits ≤ b
    exact Nat.le_trans (show minimumBits ≤ m by dsimp [m]; omega)
      (Nat.le_trans (Nat.le_of_lt mp) bl)
  · change c * b^e < (run (p*p)).probes
    omega

/-- The complete factorization budget in terms of the number of binary digits. -/
theorem probe_bound_in_bits (n : Nat) (hn : 2 ≤ n) :
    (run n).probes ≤ (2 * (bitLength n - 1) - 1) *
      (722 * 2^(2 * ((bitLength n - 1) / 6))) := by
  have bound := (run_spec n hn).2.2
  simpa only [bitLength, Nat.add_sub_cancel, scale, ← Nat.pow_mul,
              Nat.mul_comm (n.log2 / 6) 2] using bound

end CubeRootFactor

#print axioms CubeRootFactor.factorInteger_correct
#print axioms CubeRootFactor.probe_bound_in_bits
#print axioms CubeRootFactor.balanced_lower
#print axioms CubeRootFactor.exceeds_every_polynomial
