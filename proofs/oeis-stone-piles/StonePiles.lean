import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
Reachability in Peter Kagey's OEIS stone-transfer puzzle (A292726–A292728).
Gregory Igusa's 2005 related game supplies the repeated-pile observation.
Here it is proved for the exact inverse moves of the OEIS puzzle.
-/

namespace StonePiles
open Multiset

abbrev Position := Multiset ℕ

def Positive (s : Position) : Prop := ∀ x ∈ s, 0 < x

def Ones (s : Position) : Prop := ∀ x ∈ s, x = 1

def Common (d : ℕ) (s : Position) : Prop := ∀ x ∈ s, d ∣ x

/-- The pile sizes have no common odd divisor greater than one. -/
def Primitive (s : Position) : Prop := ∀ d, Odd d → Common d s → d = 1

def HasPair (s : Position) : Prop := ∃ a r, s = a ::ₘ a ::ₘ r

/-- A reverse move halves one pile or averages two different piles of the same parity. -/
inductive Undo : Position → Position → Prop
  | split (a : ℕ) (ha : 0 < a) (r : Position) :
      Undo ((a + a) ::ₘ r) (a ::ₘ a ::ₘ r)
  | average (a b t : ℕ) (hab : a ≠ b) (hsum : a + b = t + t) (r : Position) :
      Undo (a ::ₘ b ::ₘ r) (t ::ₘ t ::ₘ r)

/-- Reachability from all ones, with the recursion traversing the transfers backwards. -/
inductive Reachable : Position → Prop
  | ones {s} (h : Ones s) : Reachable s
  | step {s t} (h : Undo s t) (ht : Reachable t) : Reachable s

private def energy (s : Position) : ℕ := (s.map (fun x => x*x)).sum

private theorem common_cons {d x : ℕ} {r : Position} :
    Common d (x ::ₘ r) ↔ d ∣ x ∧ Common d r := by simp [Common]

private theorem positive_cons {x : ℕ} {r : Position} :
    Positive (x ::ₘ r) ↔ 0 < x ∧ Positive r := by simp [Positive]

private theorem ones_cons {x : ℕ} {r : Position} :
    Ones (x ::ₘ r) ↔ x = 1 ∧ Ones r := by simp [Ones]

private theorem odd_dvd_half {d x : ℕ} (hd : Odd d) (h : d ∣ x+x) : d ∣ x :=
  hd.coprime_two_right.dvd_of_dvd_mul_left (by simpa [two_mul] using h)

private theorem Undo.preserves_common {s t : Position} (h : Undo s t) {d : ℕ}
    (hd : Odd d) (hs : Common d s) : Common d t := by
  cases h with
  | split a ha r =>
    simp only [common_cons] at hs ⊢
    exact ⟨odd_dvd_half hd hs.1, odd_dvd_half hd hs.1, hs.2⟩
  | average a b t hab hsum r =>
    simp only [common_cons] at hs ⊢
    have ht : d ∣ t := odd_dvd_half hd (hsum ▸ Nat.dvd_add hs.1 hs.2.1)
    exact ⟨ht, ht, hs.2.2⟩

private theorem Undo.pair {s t : Position} (h : Undo s t) : HasPair t := by
  cases h <;> exact ⟨_, _, rfl⟩

private theorem Undo.positive {s t : Position} (h : Undo s t) (hs : Positive s) :
    Positive t := by
  cases h with
  | split a ha r =>
    exact positive_cons.mpr ⟨ha, positive_cons.mpr ⟨ha, (positive_cons.mp hs).2⟩⟩
  | average a b t hab hsum r =>
    simp only [positive_cons] at hs ⊢
    exact ⟨by omega, by omega, hs.2.2⟩

private theorem Undo.target_nonempty {s t : Position} (h : Undo s t) : t ≠ 0 := by
  obtain ⟨a, r, rfl⟩ := h.pair
  simp

private theorem Undo.energy_lt {s t : Position} (h : Undo s t) : energy t < energy s := by
  cases h with
  | split a ha r =>
    simp only [energy, map_cons, sum_cons]
    nlinarith [Nat.mul_pos ha ha]
  | average a b t hab hsum r =>
    simp only [energy, map_cons, sum_cons]
    have hne : (a : ℤ) ≠ b := by exact_mod_cast hab
    have he : (a : ℤ) + b = t + t := by exact_mod_cast hsum
    have hg : (0:ℤ) < ((a:ℤ) - b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hsq : (a:ℤ)*a + b*b > t*t + t*t := by
      nlinarith [congrArg (fun z : ℤ => z*z) he]
    have hnat : a*a + b*b > t*t + t*t := by exact_mod_cast hsq
    omega

theorem Reachable.primitive {s : Position} (h : Reachable s) (hs : s ≠ 0) : Primitive s := by
  induction h with
  | ones h =>
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hs
    intro d _ hd
    exact Nat.dvd_one.mp (h x hx ▸ hd x hx)
  | step h _ ih =>
    intro d hd hc
    exact ih h.target_nonempty d hd (h.preserves_common hd hc)

/-- A primitive position with a repeated pile can be undone all the way to ones. -/
theorem reachable_of_pair {s : Position} (pos : Positive s) (pair : HasPair s)
    (prim : Primitive s) : Reachable s := by
  classical
  by_cases ev : ∃ x ∈ s, Even x
  · obtain ⟨x, hx, k, hk⟩ := ev
    obtain ⟨r, hr⟩ := Multiset.exists_cons_of_mem hx
    subst x
    subst s
    have hpos := positive_cons.mp pos
    have hkpos : 0 < k := by omega
    have move := Undo.split k hkpos r
    apply Reachable.step move
    apply reachable_of_pair (move.positive pos) move.pair
    intro d hd h
    simp only [common_cons] at h
    exact prim d hd (common_cons.mpr ⟨Nat.dvd_add h.1 h.1, h.2.2⟩)
  · obtain ⟨a, r, rfl⟩ := pair
    have allodd : ∀ x ∈ a ::ₘ a ::ₘ r, Odd x := fun x hx =>
      Nat.not_even_iff_odd.mp (fun h => ev ⟨x, hx, h⟩)
    have haodd := allodd a (by simp)
    by_cases same : ∀ b ∈ r, b = a
    · have common_a : Common a (a ::ₘ a ::ₘ r) := by
        simp only [common_cons]
        exact ⟨dvd_rfl, dvd_rfl, fun b hb => same b hb ▸ dvd_rfl⟩
      have ha := prim a haodd common_a
      exact Reachable.ones (ones_cons.mpr ⟨ha, ones_cons.mpr ⟨ha, fun b hb => (same b hb).trans ha⟩⟩)
    · push Not at same
      obtain ⟨b, hb, hba⟩ := same
      have hbodd := allodd b (by simp [hb])
      obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hb
      obtain ⟨t, hsum⟩ := haodd.add_odd hbodd
      have perm : a ::ₘ a ::ₘ b ::ₘ u = a ::ₘ b ::ₘ a ::ₘ u := by rw [cons_swap a b u]
      have move : Undo (a ::ₘ a ::ₘ b ::ₘ u) (t ::ₘ t ::ₘ a ::ₘ u) :=
        perm.symm ▸ Undo.average a b t (Ne.symm hba) hsum (a ::ₘ u)
      apply Reachable.step move
      apply reachable_of_pair (move.positive pos) move.pair
      intro d hd h
      simp only [common_cons] at h
      have hsum' : d ∣ a + b := hsum.symm ▸ Nat.dvd_add h.1 h.1
      have hb' : d ∣ b := (Nat.dvd_add_right h.2.2.1).1 hsum'
      apply prim d hd
      simp only [common_cons]
      exact ⟨h.2.2.1, h.2.2.1, hb', h.2.2.2⟩
termination_by energy s
decreasing_by all_goals (subst_vars; exact move.energy_lt)

/-- Inspecting at most one reverse move suffices for every finite position of positive piles. -/
theorem reachable_iff {s : Position} (pos : Positive s) :
    Reachable s ↔ Ones s ∨ ∃ t, Undo s t ∧ Primitive t := by
  constructor
  · intro h
    cases h with
    | ones h => exact Or.inl h
    | step move ht => exact Or.inr ⟨_, move, ht.primitive move.target_nonempty⟩
  · rintro (ones | ⟨t, move, prim⟩)
    · exact Reachable.ones ones
    · exact Reachable.step move (reachable_of_pair (move.positive pos) move.pair prim)

private theorem common_sum {d : ℕ} {s : Position} (h : Common d s) : d ∣ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    obtain ⟨ha, hr⟩ := common_cons.mp h
    simpa using Nat.dvd_add ha (ih hr)

private theorem Undo.same_sum {s t : Position} (h : Undo s t) : s.sum = t.sum := by
  cases h <;> simp only [sum_cons] <;> omega

private theorem primitive_of_single_prime {s : Position} {p : ℕ}
    (only_prime : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ s.sum → q = p)
    (miss : ¬Common p s) : Primitive s := by
  intro d hd hds
  by_contra ne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd ne
  have hodd : q ≠ 2 := by
    rintro rfl
    obtain ⟨u, hu⟩ := hqd
    obtain ⟨v, hv⟩ := hd
    omega
  have hqs : Common q s := fun x hx => hqd.trans (hds x hx)
  have eq := only_prime q hq hodd (common_sum hqs)
  exact miss (eq ▸ hqs)

/-- For totals with at most one odd prime factor p, every position of at least
three piles with a pile not divisible by p is reachable. This is the structural
step in the two OEIS counting formulas. -/
theorem reachable_of_single_odd_prime {s : Position} {p : ℕ} (pos : Positive s)
    (size : 3 ≤ s.card) (only_prime : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ s.sum → q = p)
    (miss : ¬Common p s) : Reachable s := by
  classical
  have safe {t : Position} (move : Undo s t) (ht : ¬Common p t) : Reachable s :=
    Reachable.step move (reachable_of_pair (move.positive pos) move.pair
      (primitive_of_single_prime (fun q hq h2 hd =>
        only_prime q hq h2 (move.same_sum.symm ▸ hd)) ht))
  by_cases twins : HasPair s
  · exact reachable_of_pair pos twins (primitive_of_single_prime only_prime miss)
  by_cases ev : ∃ x ∈ s, Even x
  · obtain ⟨x, hx, k, hk⟩ := ev
    obtain ⟨r, hr⟩ := Multiset.exists_cons_of_mem hx
    subst x
    subst s
    have hkpos := (positive_cons.mp pos).1
    apply safe (Undo.split k (by omega) r)
    intro ht
    simp only [common_cons] at ht
    exact miss (common_cons.mpr ⟨Nat.dvd_add ht.1 ht.1, ht.2.2⟩)
  · have allodd : ∀ x ∈ s, Odd x := fun x hx =>
      Nat.not_even_iff_odd.mp (fun h => ev ⟨x, hx, h⟩)
    have pick : ∃ w ∈ s, ¬p ∣ w := by
      by_contra! absent
      exact miss absent
    obtain ⟨w, hw, hpw⟩ := pick
    obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hw
    have hr : r ≠ 0 := by rintro rfl; simp at size
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hr
    obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem ha
    have hr' : rest ≠ 0 := by rintro rfl; simp at size
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hr'
    obtain ⟨tail, rfl⟩ := Multiset.exists_cons_of_mem hb
    have perm : w ::ₘ a ::ₘ b ::ₘ tail = a ::ₘ b ::ₘ w ::ₘ tail := by
      calc
        _ = a ::ₘ w ::ₘ b ::ₘ tail := cons_swap _ _ _
        _ = _ := congrArg (fun r => a ::ₘ r) (cons_swap w b tail)
    have hab : a ≠ b := by rintro rfl; exact twins ⟨a, _, perm⟩
    have haodd := allodd a (by simp)
    have hbodd := allodd b (by simp)
    obtain ⟨t, hsum⟩ := haodd.add_odd hbodd
    apply safe (t := t ::ₘ t ::ₘ w ::ₘ tail) (perm.symm ▸ Undo.average a b t hab hsum _)
    exact fun h => hpw (h w (by simp))

end StonePiles

#print axioms StonePiles.reachable_iff

#print axioms StonePiles.reachable_of_single_odd_prime
