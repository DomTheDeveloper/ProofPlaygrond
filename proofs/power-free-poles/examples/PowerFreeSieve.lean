module

public import Init

@[expose] public section

namespace PowerFree.Sieve

/-- Count the positive integers through N passing a Boolean predicate. -/
def countUpTo (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countUpTo P n + if P (n+1) then 1 else 0

/-- Reject every listed divisor. -/
def avoids (ds : List Nat) (j : Nat) : Bool := ds.all fun d => !(decide (d ∣ j))

private def filtered (ds : List Nat) (a n : Nat) :=
  countUpTo (fun j => decide (a ∣ j) && avoids ds j) n

private theorem filtered_nil (a n : Nat) : filtered [] a n = n / a := by
  induction n with
  | zero => simp [filtered, countUpTo]
  | succ n ih =>
    change filtered [] a n + _ = _
    by_cases h : a ∣ n+1
    · simp [filtered, avoids, h, Nat.succ_div_of_dvd h] at ih ⊢
      exact ih
    · simp [filtered, avoids, h, Nat.succ_div_of_not_dvd h] at ih ⊢
      exact ih

private theorem split_count (ds : List Nat) (d a n : Nat) :
    filtered (d::ds) a n + filtered ds (Nat.lcm a d) n = filtered ds a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (filtered (d::ds) a n + _) + (filtered ds (Nat.lcm a d) n + _) = filtered ds a n + _
    by_cases ha : a ∣ n+1 <;> by_cases hd : d ∣ n+1 <;> cases hv : avoids ds (n+1) <;>
      simp [avoids, List.all_cons, Nat.lcm_dvd_iff, ha, hd] at hv ⊢ <;> omega

/-- Inclusion-exclusion applied to multiples of a. A divisor above N has no positive multiples. -/
def countAvoiding : List Nat → Nat → Nat → Nat
  | [], a, N => N / a
  | d :: ds, a, N => if N < a then 0 else
      countAvoiding ds a N - countAvoiding ds (Nat.lcm a d) N

private theorem filtered_zero_of_lt (ds : List Nat) {a N : Nat} (h : N < a) : filtered ds a N = 0 := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have hd : ¬ a ∣ n+1 := fun hdiv => (Nat.not_le_of_lt h) (Nat.le_of_dvd (by omega) hdiv)
    change filtered ds a n + _ = 0
    simp [hd, ih (by omega)]

/-- The floor-division recurrence counts exactly the allowed integers. -/
theorem countAvoiding_eq (ds : List Nat) (a N : Nat) :
    countAvoiding ds a N = countUpTo (fun j => decide (a ∣ j) && avoids ds j) N := by
  change _ = filtered ds a N
  induction ds generalizing a with
  | nil => exact (filtered_nil a N).symm
  | cons d ds ih =>
    rw [countAvoiding]
    split
    · rename_i h
      exact (filtered_zero_of_lt (d::ds) h).symm
    · rw [ih, ih]
      have h := split_count ds d a N
      omega

/-- The list includes precisely the powers with base at least two that can divide
some positive integer at most N. Composite bases are harmless. -/
def forbidden (k N : Nat) : List Nat :=
  ((List.range (N+1)).filter (fun d => decide (2 ≤ d ∧ d^k ≤ N))).map (fun d => d^k)

/-- A mathematical specification independent of the sieve implementation. -/
def IsPowerFree (k n : Nat) : Prop := ∀ d, 2 ≤ d → ¬d^k ∣ n

/-- The bounded divisor test recognizes the unbounded mathematical predicate. -/
theorem avoids_iff {k N j : Nat} (hk : 0 < k) (hj : 0 < j) (hN : j ≤ N) :
    avoids (forbidden k N) j = true ↔ IsPowerFree k j := by
  simp only [avoids, forbidden, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h d hd hdiv
    have hp : d^k ≤ j := Nat.le_of_dvd hj hdiv
    have hd' : d ≤ d^k := by
      have := Nat.pow_le_pow_right (by omega : 0 < d) (by omega : 1 ≤ k)
      simpa using this
    exact h _ ⟨d, ⟨by omega, hd, by omega⟩, rfl⟩ hdiv
  · rintro h _ ⟨d, ⟨_, hd, _⟩, rfl⟩
    exact h d hd

/-- Exact power-free counts from floors and least common multiples. -/
def powerFreeCount (k N : Nat) := countAvoiding (forbidden k N) 1 N

theorem powerFreeCount_eq (k N : Nat) :
    powerFreeCount k N = countUpTo (avoids (forbidden k N)) N := by
  simp [powerFreeCount, countAvoiding_eq]

end PowerFree.Sieve
