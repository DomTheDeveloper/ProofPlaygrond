import Std

/-!
# Counting two deterministic factoring searches

This file uses Lean 4.19.0 and the standard library. Run
`lean FactoringSearchBounds.lean` to check it.

`factorFrom` follows the branches in the supplied Lean transcript and records
one test each time it evaluates a remainder. `fermat` counts candidate
midpoints. Each midpoint uses a binary integer square root. The two counts
measure different operations.

* `trial_all_semiprimes` gives the exact remainder count for p*q.
* `fermat_exact` and `fermat_gap_bound` locate the first successful midpoint
  and bound the cost on close prime factors.
* `fermat_separated_primes` gives a linear lower bound in the smaller prime
  when the primes have ratio between two and four.
* `bounded_multiplier_count` bounds how many inputs can give even one exact
  square when the multiplier and midpoint offset are both bounded.

The elementary bit-complexity and prime-counting deductions from these
theorems are given in the closing note.
-/

namespace FactoringSearchBounds

def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

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

private theorem semiprime_divisors {p q d : Nat} (hp : Prime p) (hq : Prime q)
    (divides : d ∣ p*q) : d = 1 ∨ d = p ∨ d = q ∨ d = p*q := by
  obtain ⟨u, v, hu, hv, uv⟩ := Nat.dvd_mul.mp divides
  rcases hp.2 u hu with h | h <;> rcases hq.2 v hv with k | k <;>
    simp_all

/-! ## Trial division -/

structure TrialRun where
  factors : List Nat
  tests : Nat
  deriving Repr, DecidableEq

def factorFrom (d n : Nat) : TrialRun :=
  if h : 2 ≤ d ∧ d*d ≤ n then
    if n % d = 0 then
      let tail := factorFrom d (n / d)
      ⟨d :: tail.factors, tail.tests + 1⟩
    else
      let tail := factorFrom (d + 1) n
      ⟨tail.factors, tail.tests + 1⟩
  else
    ⟨if 2 ≤ n then [n] else [], 0⟩
termination_by (n, n + 1 - d)
decreasing_by
  · apply Prod.Lex.left
    have dn := Nat.le_trans (le_square (Nat.le_trans (by decide : 1 ≤ 2) h.1)) h.2
    exact Nat.div_lt_self (by omega) (by omega)
  · apply Prod.Lex.right
    have dn := Nat.le_trans (le_square (Nat.le_trans (by decide : 1 ≤ 2) h.1)) h.2
    omega

private theorem trial_to_factor {p q : Nat} (hp : Prime p) (hq : Prime q)
    (ordered : p ≤ q) (d : Nat) (start : 2 ≤ d) (stop : d ≤ p) :
    factorFrom d (p*q) =
      let tail := factorFrom p q
      ⟨p :: tail.factors, (p-d+1) + tail.tests⟩ := by
  have pp := hp.1
  have qq := hq.1
  have live : 2 ≤ d ∧ d*d ≤ p*q := ⟨start, Nat.mul_le_mul stop (by omega)⟩
  by_cases atFactor : d = p
  · subst d
    have divides := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right p q)
    rw [factorFrom, dif_pos live, if_pos divides, Nat.mul_div_cancel_left q (by omega)]
    simp [Nat.add_comm]
  · have miss : ¬ (p*q) % d = 0 := by
      intro hit
      have cases := semiprime_divisors hp hq (Nat.dvd_of_mod_eq_zero hit)
      have prod : p ≤ p*q := by simpa using Nat.mul_le_mul_left p (show 1 ≤ q by omega)
      omega
    have rec := trial_to_factor hp hq ordered (d+1) (by omega) (by omega)
    rw [factorFrom, dif_pos live, if_neg miss, rec]
    simp only [TrialRun.mk.injEq, true_and]
    omega
termination_by p-d

/-- For p ≤ q < p², the entire run uses exactly p−1 remainders. -/
theorem trial_semiprime {p q : Nat} (hp : Prime p) (hq : Prime q)
    (ordered : p ≤ q) (short : q < p*p) :
    factorFrom 2 (p*q) = ⟨[p,q], p-1⟩ := by
  have stop : ¬ (2 ≤ p ∧ p*p ≤ q) := by omega
  have tail : factorFrom p q = ⟨[q], 0⟩ := by
    rw [factorFrom, dif_neg stop, if_pos hq.1]
  rw [trial_to_factor hp hq ordered 2 (by decide) hp.1, tail]
  have := hp.1
  simp only [Nat.add_zero, TrialRun.mk.injEq, true_and]
  omega

theorem trial_prime_square {p : Nat} (hp : Prime p) :
    factorFrom 2 (p*p) = ⟨[p,p], p-1⟩ := by
  have pp := hp.1
  have h := Nat.mul_le_mul_left p pp
  exact trial_semiprime hp hp (Nat.le_refl _) (by omega)

/-! ## Binary floor and ceiling square roots -/

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

def ceilRoot (n : Nat) : Nat :=
  let r := floorRoot n
  if r*r = n then r else r+1

theorem ceilRoot_covers (n : Nat) : n ≤ ceilRoot n * ceilRoot n := by
  obtain ⟨_, hi⟩ := floorRoot_bounds n
  simp only [ceilRoot]
  split <;> omega

theorem ceilRoot_le {n x : Nat} (covers : n ≤ x*x) : ceilRoot n ≤ x := by
  obtain ⟨lo, _⟩ := floorRoot_bounds n
  have rx := le_of_square_le (Nat.le_trans lo covers)
  simp only [ceilRoot]
  split
  · exact rx
  · rename_i strict
    by_cases eq : x = floorRoot n
    · subst x; omega
    · omega

private theorem prime_tail {q : Nat} (hq : Prime q) (d : Nat) (hd : 2 ≤ d) :
    factorFrom d q = ⟨[q], floorRoot q + 1 - d⟩ := by
  obtain ⟨lo, hi⟩ := floorRoot_bounds q
  by_cases live : d*d ≤ q
  · have dq : d < q := by have := Nat.mul_le_mul_left d hd; omega
    have dr : d ≤ floorRoot q := by
      apply Nat.le_of_not_gt
      intro no
      have := square_le (show floorRoot q+1 ≤ d by omega)
      omega
    have miss : ¬ q % d = 0 := by
      intro hit
      rcases hq.2 d (Nat.dvd_of_mod_eq_zero hit) with eq | eq <;> omega
    rw [factorFrom, dif_pos ⟨hd,live⟩, if_neg miss, prime_tail hq (d+1) (by omega)]
    simp only [TrialRun.mk.injEq, true_and]
    omega
  · have quit : ¬ (2 ≤ d ∧ d*d ≤ q) := fun h => live h.2
    have rd : floorRoot q < d := by
      apply Nat.lt_of_not_ge
      intro no
      exact live (Nat.le_trans (square_le no) lo)
    rw [factorFrom, dif_neg quit, if_pos hq.1]
    simp only [TrialRun.mk.injEq, true_and]
    omega
termination_by q+1-d

/-- Exact count on every product of two ordered primes, with repetition allowed. -/
theorem trial_all_semiprimes {p q : Nat} (hp : Prime p) (hq : Prime q) (ordered : p ≤ q) :
    factorFrom 2 (p*q) = ⟨[p,q], max (p-1) (floorRoot q)⟩ := by
  rw [trial_to_factor hp hq ordered 2 (by decide) hp.1, prime_tail hq p hp.1]
  have := hp.1
  simp only [TrialRun.mk.injEq, true_and]
  omega

/-- A dyadic lower bound expressed in the binary length of the input p². -/
theorem trial_prime_square_exponential {p : Nat} (hp : Prime p) :
    2^((p*p).log2/2) ≤ (factorFrom 2 (p*p)).tests + 1 := by
  rw [trial_prime_square hp]
  have pp : 0 < p := by have := hp.1; omega
  have hh := (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos pp pp))).1 (Nat.le_refl (p*p).log2)
  have exps : (p*p).log2/2 + (p*p).log2/2 ≤ (p*p).log2 := by omega
  have two := Nat.pow_le_pow_right (by decide : 0 < 2) exps
  rw [Nat.pow_add] at two
  have := le_of_square_le (Nat.le_trans two hh)
  change 2^((p*p).log2/2) ≤ p-1+1
  omega

/-! ## Midpoint search by differences of squares -/

def probe (n a : Nat) : Option (Nat × Nat) :=
  let h := floorRoot (a*a - n)
  let u := a-h
  let v := a+h
  if 2 ≤ u ∧ u*v = n then some (u,v) else none

private theorem probe_facts {n a u v : Nat} (hit : probe n a = some (u,v)) :
    2 ≤ u ∧ u ≤ v ∧ u*v = n ∧ u+v = 2*a := by
  dsimp only [probe] at hit
  split at hit
  · rename_i ok
    cases hit
    exact ⟨ok.1, by omega, ok.2, by have := ok.1; omega⟩
  · contradiction

private theorem unique_pair {p q u v : Nat} (hp : Prime p) (hq : Prime q)
    (ordered : p ≤ q) (nontrivial : 2 ≤ u) (sorted : u ≤ v) (prod : u*v = p*q) :
    u = p ∧ v = q := by
  have ud : u ∣ p*q := prod ▸ Nat.dvd_mul_right u v
  rcases semiprime_divisors hp hq ud with one | left | right | whole
  · omega
  · subst u
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) prod⟩
  · subst u
    rw [Nat.mul_comm p q] at prod
    have same := Nat.eq_of_mul_eq_mul_left (by omega) prod
    omega
  · have h : u*v = u*1 := by rw [prod, Nat.mul_one, whole]
    have := Nat.eq_of_mul_eq_mul_left (by omega) h
    omega

private theorem midpoint_square (p h : Nat) :
    (p+h)*(p+h) = p*(p+2*h) + h*h := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_left_comm p 2 h, Nat.mul_comm h p]
  omega

private theorem probe_midpoint (p h : Nat) (hp : 2 ≤ p) :
    probe (p*(p+2*h)) (p+h) = some (p,p+2*h) := by
  have delta : (p+h)*(p+h) - p*(p+2*h) = h*h := by
    have := midpoint_square p h
    omega
  simp only [probe, delta, floorRoot_square, Nat.add_sub_cancel]
  rw [show p+h+h = p+2*h by omega, if_pos ⟨hp, rfl⟩]

private theorem probe_before {p h a : Nat} (hp : Prime p) (hq : Prime (p+2*h))
    (early : a < p+h) : probe (p*(p+2*h)) a = none := by
  cases e : probe (p*(p+2*h)) a with
  | none => rfl
  | some pair =>
    obtain ⟨u,v⟩ := pair
    obtain ⟨nontrivial, sorted, prod, sum⟩ := probe_facts e
    obtain ⟨_,_⟩ := unique_pair hp hq (by omega) nontrivial sorted prod
    omega

structure FermatRun where
  result : Option (Nat × Nat)
  tests : Nat
  deriving Repr, DecidableEq

def scan (n a : Nat) : Nat → FermatRun
  | 0 => ⟨none,0⟩
  | fuel+1 =>
    match probe n a with
    | some pair => ⟨some pair,1⟩
    | none =>
      let tail := scan n (a+1) fuel
      ⟨tail.result,tail.tests+1⟩

private theorem scan_first {n midpoint : Nat} {pair : Nat × Nat}
    (hit : probe n midpoint = some pair) (early : ∀ a, a < midpoint → probe n a = none)
    (fuel a : Nat) (start : a ≤ midpoint) :
    scan n a fuel = if midpoint < a+fuel then ⟨some pair,midpoint-a+1⟩ else ⟨none,fuel⟩ := by
  induction fuel generalizing a with
  | zero =>
    have no : ¬ midpoint < a+0 := by omega
    simp [scan, no, Nat.not_lt_of_ge start]
  | succ k ih =>
    by_cases same : a = midpoint
    · subst a
      have yes : midpoint < midpoint+(k+1) := by omega
      simp [scan, hit, yes]
    · have miss := early a (by omega)
      have next := ih (a+1) (by omega)
      have edges : (a+1)+k = a+(k+1) := by omega
      rw [edges] at next
      by_cases yes : midpoint < a+(k+1)
      · rw [if_pos yes] at next ⊢
        simp only [scan, miss, next, FermatRun.mk.injEq, true_and]
        omega
      · rw [if_neg yes] at next ⊢
        simp [scan, miss, next]

/-- Search from ⌈√n⌉ through ⌈√n⌉ + window, including both endpoints. -/
def fermat (n window : Nat) : FermatRun := scan n (ceilRoot n) (window+1)

/-- For p and p+2h prime, the window contains a successful midpoint exactly
when it reaches p+h. This computes both the returned factors and the test count. -/
theorem fermat_exact {p h : Nat} (hp : Prime p) (hq : Prime (p+2*h)) (w : Nat) :
    let n := p*(p+2*h)
    let r := ceilRoot n
    fermat n w = if p+h ≤ r+w then ⟨some (p,p+2*h),p+h-r+1⟩ else ⟨none,w+1⟩ := by
  let n := p*(p+2*h)
  let r := ceilRoot n
  have low : r ≤ p+h := by
    apply ceilRoot_le
    dsimp [n]
    have := midpoint_square p h
    omega
  have counted := scan_first (probe_midpoint p h hp.1)
    (fun _ e => probe_before hp hq e) (w+1) r low
  have edge : p+h < r+(w+1) ↔ p+h ≤ r+w := by omega
  simp only [edge] at counted
  exact counted

/-- A checkable integer version of the close-factor bound. With w polynomial
in the input length, the routine uses at most w+1 square-root probes. -/
theorem fermat_gap_bound {p h : Nat} (hp : Prime p) (hq : Prime (p+2*h)) (w : Nat)
    (close : h*h ≤ 2*ceilRoot (p*(p+2*h))*w) :
    let n := p*(p+2*h)
    (fermat n w).result = some (p,p+2*h) ∧ (fermat n w).tests ≤ w+1 := by
  let n := p*(p+2*h)
  let r := ceilRoot n
  have gap : h*h ≤ 2*r*w := close
  have cover : n ≤ r*r := ceilRoot_covers n
  have added : (r+w)*(r+w) = r*r+2*r*w+w*w := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm w r]
    omega
  have reach : p+h ≤ r+w := by
    apply le_of_square_le
    have center : (p+h)*(p+h) = n+h*h := midpoint_square p h
    omega
  have run := fermat_exact hp hq w
  change fermat n w = if p+h ≤ r+w then _ else _ at run
  rw [if_pos reach] at run
  change (fermat n w).result = _ ∧ (fermat n w).tests ≤ _
  rw [run]
  exact ⟨rfl, by change p+h-r+1 ≤ w+1; omega⟩

/-! ## How many inputs can small multipliers cover?

Allow every multiplier 1 ≤ k ≤ K and every midpoint through ⌈√(kn)⌉ + w.
Any square hit, including one that only gives a trivial factor, must have
kn + y² = a². The following finite counting bound applies even to an adaptive
choice of the multiplier and midpoint within those ranges.
-/

/-- A square hit among the permitted multipliers and midpoints. -/
def HasWindowHit (n K w : Nat) : Prop :=
  ∃ k a y, 0 < k ∧ k ≤ K ∧ a ≤ ceilRoot (k*n)+w ∧ a*a = k*n + y*y

private theorem pred_ceil_lower {n : Nat} (pos : 0 < n) :
    (ceilRoot n-1)*(ceilRoot n-1) < n := by
  have rp : 0 < ceilRoot n := by
    cases e : ceilRoot n with
    | zero => have := ceilRoot_covers n; rw [e] at this; omega
    | succ t => omega
  apply Nat.lt_of_not_ge
  intro covers
  have := ceilRoot_le covers
  omega

private theorem square_increment (u t : Nat) :
    (u+t)*(u+t) ≤ u*u + 2*(u+t)*t := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm t u]
  omega

private theorem gap_square_lt {n a y w : Nat} (pos : 0 < n)
    (near : a ≤ ceilRoot n+w) (square : a*a = n+y*y) :
    y*y < 2*a*(w+1) := by
  let u := ceilRoot n-1
  let t := a-u
  have predecessor : u*u < n := pred_ceil_lower pos
  have start : ceilRoot n ≤ a := ceilRoot_le (by omega : n ≤ a*a)
  have reach : u+t = a := by dsimp [u,t]; omega
  have width : t ≤ w+1 := by dsimp [t,u]; omega
  have step := square_increment u t
  rw [reach] at step
  have extend := Nat.mul_le_mul_left (2*a) width
  omega

/-- For 2p ≤ q ≤ 4p, a successful search needs more than p/20 midpoints. -/
theorem fermat_separated_primes {p h : Nat} (hp : Prime p) (hq : Prime (p+2*h))
    (lower : 2*p ≤ p+2*h) (upper : p+2*h ≤ 4*p) (w : Nat)
    (found : (fermat (p*(p+2*h)) w).result ≠ none) :
    p < 20*(fermat (p*(p+2*h)) w).tests := by
  let n := p*(p+2*h)
  let r := ceilRoot n
  let s := p+h
  let t := s-r+1
  have pp := hp.1
  have pos : 0 < n := Nat.mul_pos (by omega) (by omega)
  have center : s*s = n+h*h := midpoint_square p h
  have start : r ≤ s := ceilRoot_le (by omega)
  have hsq : h*h < 2*s*t := gap_square_lt (n := n) (a := s) (y := h) (w := s-r)
    pos (by change s ≤ r+(s-r); omega) center
  have scale := Nat.mul_le_mul_right t (show 2*s ≤ 5*p by dsimp [s]; omega)
  have bound : p*p < p*(20*t) := calc
    p*p ≤ (2*h)*(2*h) := square_le (by omega)
    _ = 4*(h*h) := Nat.mul_mul_mul_comm 2 h 2 h
    _ < 4*(5*p*t) := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_lt_of_le hsq scale) (by decide)
    _ = (4*5)*(p*t) := by ac_rfl
    _ = p*(20*t) := Nat.mul_left_comm 20 p t
  have exactRun := fermat_exact hp hq w
  change fermat n w = if s ≤ r+w then _ else _ at exactRun
  change (fermat n w).result ≠ none at found
  change p < 20*(fermat n w).tests
  by_cases fits : s ≤ r+w
  · rw [if_pos fits] at exactRun
    rw [exactRun]
    exact Nat.lt_of_mul_lt_mul_left bound
  · rw [if_neg fits] at exactRun
    exact False.elim (found (by rw [exactRun]))

/-- The possible square identities lie in a finite box. R sets the input
scale n ≤ R⁴. A midpoint has size O(K R²), and y has size O(K(w+1)R). -/
private theorem witness_bounds {n K w R k a y : Nat} (positive : 0 < n)
    (size : n ≤ (R*R)*(R*R)) (smallWindow : w ≤ R*R)
    (kp : 0 < k) (small : k ≤ K) (near : a ≤ ceilRoot (k*n)+w)
    (square : a*a = k*n+y*y) :
    a ≤ (K+1)*(R*R) ∧ y ≤ (2*(K+1)*(w+1))*R := by
  let m := R*R
  have kk : k ≤ K*K := Nat.le_trans small (le_square (by omega))
  have rootCap : ceilRoot (k*n) ≤ K*m := by
    apply ceilRoot_le
    rw [Nat.mul_mul_mul_comm K m K m]
    exact Nat.mul_le_mul kk size
  have cap : a ≤ (K+1)*m := by
    rw [Nat.succ_mul]
    change w ≤ m at smallWindow
    omega
  let C := 2*(K+1)*(w+1)
  have ySq : y*y ≤ C*m := calc
    y*y ≤ 2*a*(w+1) := Nat.le_of_lt (gap_square_lt (Nat.mul_pos kp positive) near square)
    _ ≤ 2*((K+1)*m)*(w+1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cap)
    _ = C*m := by dsimp [C]; ac_rfl
  have cp : 0 < C := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
  refine ⟨cap, le_of_square_le ?_⟩
  change y*y ≤ (C*R)*(C*R)
  rw [Nat.mul_mul_mul_comm C R C R]
  exact Nat.le_trans ySq (Nat.mul_le_mul_right _ (le_square cp))

/-- Each triple (k,a,y) names at most one integer, (a²−y²)/k. Duplicates
and non-witnesses are harmless in this upper bound. -/
private def boxValues (K A H : Nat) : List Nat :=
  (List.range K).flatMap fun i =>
    (List.range (A+1)).flatMap fun a =>
      (List.range (H+1)).map fun y => (a*a-y*y)/(i+1)

private theorem uniform_length {α β : Type} (f : α → List β) (m : Nat)
    (each : ∀ x, (f x).length = m) (xs : List α) :
    (xs.flatMap f).length = xs.length*m := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, each, ih, Nat.succ_mul, Nat.add_comm]

private theorem box_length (K A H : Nat) :
    (boxValues K A H).length = K*((A+1)*(H+1)) := by
  unfold boxValues
  rw [uniform_length _ ((A+1)*(H+1))]
  · simp
  · intro i
    rw [uniform_length _ (H+1)]
    · simp
    · intro a
      simp

private theorem nodup_bound {xs ys : List Nat} (distinct : xs.Nodup)
    (inside : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp distinct
    have present := inside x (by simp)
    have after : xs.length ≤ (ys.erase x).length := by
      apply ih rest
      intro v mem
      have ne : v ≠ x := by intro eq; subst v; exact fresh mem
      exact (List.mem_erase_of_ne ne).2 (inside v (List.mem_cons_of_mem _ mem))
    rw [List.length_erase_of_mem present] at after
    have := List.length_pos_of_mem present
    simp only [List.length_cons]
    omega

/-- This counts distinct positive inputs up to R⁴ having even one hit. -/
theorem bounded_multiplier_count (K w R : Nat) (smallWindow : w ≤ R*R)
    (inputs : List Nat) (distinct : inputs.Nodup)
    (hits : ∀ n ∈ inputs, 0 < n ∧ n ≤ (R*R)*(R*R) ∧ HasWindowHit n K w) :
    let A := (K+1)*(R*R)
    let H := (2*(K+1)*(w+1))*R
    inputs.length ≤ K*((A+1)*(H+1)) := by
  let A := (K+1)*(R*R)
  let H := (2*(K+1)*(w+1))*R
  suffices allIn : ∀ n ∈ inputs, n ∈ boxValues K A H by
    change inputs.length ≤ K*((A+1)*(H+1))
    rw [← box_length K A H]
    exact nodup_bound distinct allIn
  intro n hn
  obtain ⟨np, size, k, a, y, kp, small, near, square⟩ := hits n hn
  obtain ⟨aCap, yCap⟩ := witness_bounds np size smallWindow kp small near square
  change a ≤ A at aCap
  change y ≤ H at yCap
  unfold boxValues
  apply List.mem_flatMap.mpr
  refine ⟨k-1, List.mem_range.mpr (by omega), List.mem_flatMap.mpr ?_⟩
  refine ⟨a, List.mem_range.mpr (by omega), List.mem_map.mpr ?_⟩
  refine ⟨y, List.mem_range.mpr (by omega), ?_⟩
  have delta : a*a-y*y = k*n := by omega
  rw [delta, show k-1+1 = k by omega, Nat.mul_div_cancel_left n kp]

/-!
## Consequences for binary running time

Let b = floor(log₂ n) + 1 for n ≥ 2. On the infinite sequence of prime
squares, trial division takes exactly √n − 1 remainder tests.

For an odd semiprime n = p*q, write s = (p+q)/2 and r = ⌈√n⌉. The number
of probes through the first success is 1+s−r. Rationalizing s−√n gives

    s−√n = (q−p)² / (4(s+√n)) ≤ (q−p)² / (8√n).

In particular, fix a nonnegative integer c. If q−p ≤ n^(1/4) b^c, the
search with window b^(2c) returns p and q. It tries at most
1 + floor(b^(2c)/8) midpoints. Each successful run examines midpoints
at most s ≤ n. The binary root routine therefore takes O(b) rounds per
probe, on O(b)-bit integers. Schoolbook multiplication and computing 2^k
by a shift give O(b²) bit operations per round. This gives the classical
bound O((1+b^(2c)) b³) on that promised family. The file verifies the
search results, root bounds and probe counts. The bit-cost conversion here
uses ordinary binary arithmetic.

For the counting theorem take X = R⁴. For K ≥ 1 and R ≥ 1, its finite
bound is O(K(K+1)²(w+1)R³). With both K and w polynomial in log X,
at most X^(3/4) (log X)^O(1) distinct integers up to X can have any hit.
For arbitrary X take R = ⌈X^(1/4)⌉. By the prime number theorem there are
Θ(√X/log X) primes in [√X/2, √X]. Unordered pairs of distinct primes in
this interval give Θ(X/(log X)²) distinct semiprimes by unique
factorization. The proportion with any hit is at most
X^(−1/4) (log X)^O(1), which tends to zero. This deduction uses the prime
number theorem externally. The finite bound itself is proved above.

Background on Fermat's method and multiplier variants is in W. B. Hart,
“A One Line Factoring Algorithm.”
https://doi.org/10.1017/S1446788712000146

For the prime number theorem see the Harvard Math 113 lecture notes.
https://people.math.harvard.edu/archive/113_fall_01/113pnt.pdf
-/

end FactoringSearchBounds
