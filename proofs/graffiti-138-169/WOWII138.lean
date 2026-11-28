import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

/-!
# A counterexample to Written on the Wall II, conjecture 138

Ermelinda DeLaViña, July 12, 2005. The conjecture bounds the order of a longest
induced path below by `(2 + u(G)) * d`, where `u(G)` records uniqueness of a
maximum independent set and `d` is the minimum distance between distinct
maximum-degree vertices of the square graph. A 19-vertex tree has values
17, 1, and 6, respectively. The six-edge route in the square runs from 2 to 14.

Source: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html
The catalog's definition heading calls `u` the unique maximum independent set indicator.

Checked with Lean 4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.
-/
set_option autoImplicit false

namespace WOWII138
open SimpleGraph

/-- In the square, distinct vertices are adjacent if they are one or two steps apart. -/
def square {V : Type*} (H : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm)
    (fun ⟨z, e, f⟩ => Or.inr ⟨z, f.symm, e.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : DecidableRel (square H).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∨ ∃ z, H.Adj _ z ∧ H.Adj z _)))

def MaxDeg {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) : Prop :=
  ∀ w, H.degree w ≤ H.degree v

/-- Distances of all distinct pairs of maximum-degree vertices in a graph. -/
def pairDistances {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] : Set ℕ :=
  {d | ∃ x y, x ≠ y ∧ MaxDeg H x ∧ MaxDeg H y ∧ H.dist x y = d}

open scoped Classical in
noncomputable def uniqueFlag {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  if ∃! S : Finset V, H.IsMaximumIndepSet S then 1 else 0

def inducedPathOrders {V : Type*} (H : SimpleGraph V) : Set ℕ :=
  {k | ∃ (x y : V) (p : H.Walk x y), p.IsPath ∧ p.IsChordless ∧ p.length + 1 = k}

/-- The published claim for finite graphs, using a minimum only when the pair exists. -/
def Conjecture138 : Prop := ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
  H.Connected → ∀ d, IsLeast (pairDistances (square H)) d →
    ∃ k ∈ inducedPathOrders H, (2 + uniqueFlag H) * d ≤ k

abbrev V := Fin 19

/-- The path 0–1–…–16, plus leaves 17 at 1 and 18 at 15. -/
def G : SimpleGraph V := SimpleGraph.fromRel fun a b =>
  (a.val + 1 = b.val ∧ b.val ≤ 16) ∨ (a = 1 ∧ b = 17) ∨ (a = 15 ∧ b = 18)

instance : DecidableRel G.Adj := fun a b => by unfold G; rw [fromRel_adj]; infer_instance

private def column (v : V) : ℕ := if v = 17 then 0 else if v = 18 then 16 else v.val
private def depth (v : V) : ℕ := (column v - 8) + (8 - column v)
private def parent (v : V) : V := if v = 17 then 1 else if v = 18 then 15
  else if v.val < 8 then v + 1 else v - 1

private theorem towardCenter : ∀ v : V, v ≠ 8 →
    G.Adj v (parent v) ∧ depth (parent v) + 1 = depth v := by decide

private theorem nearCenter (v : V) : ∃ p : G.Walk v 8, p.length = depth v := by
  by_cases h : v = 8
  · subst v; exact ⟨.nil, by decide⟩
  · obtain ⟨edge, drop⟩ := towardCenter v h
    obtain ⟨p, hp⟩ := nearCenter (parent v)
    exact ⟨p.cons edge, by simpa [hp] using drop⟩
termination_by depth v
decreasing_by omega

theorem connected : G.Connected := by
  have reach : ∀ u v : V, G.Reachable u v := by
    intro u v
    obtain ⟨p, _⟩ := nearCenter u
    obtain ⟨q, _⟩ := nearCenter v
    exact p.reachable.trans q.reachable.symm
  exact { preconnected := reach, nonempty := ⟨8⟩ }

theorem tree : G.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
  decide

private theorem pathBound {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length + 1 ≤ 17 := by
  obtain ⟨q, hq, hlen⟩ := connected.exists_path_of_dist u v
  have eqp : p = q := Subtype.mk.inj ((tree.isAcyclic.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩)
  obtain ⟨pu, hu⟩ := nearCenter u
  obtain ⟨pv, hv⟩ := nearCenter v
  have hdist := SimpleGraph.dist_le (pu.append pv.reverse)
  have hdepth : ∀ x : V, depth x ≤ 8 := by decide
  rw [Walk.length_append, Walk.length_reverse, hu, hv] at hdist
  rw [eqp, hlen]
  have := hdepth u
  have := hdepth v
  omega

private def spine : G.Walk 0 16 :=
  Walk.ofSupport ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List V)
    (by decide) (by decide)

theorem longestInducedPath : IsGreatest (inducedPathOrders G) 17 := by
  refine ⟨⟨0, 16, spine, (Walk.isPath_def spine).2 (by decide), ?_, by decide⟩, ?_⟩
  · rw [Walk.isChordless_iff_forall_mem_edges]
    decide
  · rintro k ⟨x, y, p, hp, _, rfl⟩
    exact pathBound hp

/-- The larger side of the bipartition. -/
private def evenSide : Finset V := Finset.univ.filter fun v => v.val % 2 = 0 ∨ 17 ≤ v.val

/-- Pair every odd spine vertex with an even neighbor, pointing away from `avoid`.
Each fiber has one vertex or two adjacent vertices. The avoided even-side vertex is alone. -/
private def representative (avoid v : V) : V :=
  if v.val < 17 ∧ v.val % 2 = 1 then if v.val < avoid.val then v - 1 else v + 1 else v

set_option maxRecDepth 8192 in
private theorem representativeFacts : ∀ a : V, a ∈ evenSide →
    (∀ v, representative a v ∈ evenSide) ∧
    (∀ v, representative a v = a → v = a) ∧
    (∀ v w, representative a v = representative a w → v = w ∨ G.Adj v w) := by decide

private theorem images (S : Finset V) (hi : G.IsIndepSet S) {a : V} (ha : a ∈ evenSide) :
    S.image (representative a) ⊆ evenSide ∧ (S.image (representative a)).card = S.card := by
  obtain ⟨target, _, collision⟩ := representativeFacts a ha
  refine ⟨Finset.image_subset_iff.mpr (fun v _ => target v), Finset.card_image_of_injOn ?_⟩
  intro v hv w hw h
  exact (collision v w h).resolve_right (fun e => hi hv hw e.ne e)

private theorem largestEven : G.IsMaximumIndepSet evenSide := by
  refine ⟨by decide, fun S hi => ?_⟩
  obtain ⟨sub, hc⟩ := images S hi (a := 0) (by decide)
  exact hc ▸ Finset.card_le_card sub

theorem independenceNumber : G.indepNum = 11 := by
  calc G.indepNum = evenSide.card := (maximumIndepSet_card_eq_indepNum evenSide largestEven).symm
       _ = 11 := by decide

theorem uniqueMaximum : ∃! S : Finset V, G.IsMaximumIndepSet S := by
  refine ⟨evenSide, largestEven, fun S hm => ?_⟩
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le _ (largestEven.maximum S hm.isIndepSet)
  intro a ha
  obtain ⟨sub, hc⟩ := images S hm.isIndepSet ha
  have size := hm.maximum evenSide largestEven.isIndepSet
  have cover := Finset.eq_of_subset_of_card_le sub (hc ▸ size)
  obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp (cover ▸ ha : a ∈ S.image (representative a))
  exact (representativeFacts a ha).2.1 v eq ▸ hv

private def squareDegree (v : V) : ℕ :=
  if v = 2 ∨ v = 14 then 5 else if v = 0 ∨ 16 ≤ v.val then 3 else 4

private theorem squareDegreeTable : ∀ v : V, (square G).degree v = squareDegree v := by decide

theorem maxVertices : ∀ v : V, MaxDeg (square G) v ↔ v = 2 ∨ v = 14 := by
  unfold MaxDeg
  simp only [squareDegreeTable]
  decide

theorem maximumSquareDegree : (square G).degree 2 = 5 ∧ (square G).degree 14 = 5 := by
  rw [squareDegreeTable, squareDegreeTable]
  decide

private theorem stepBound : ∀ u v : V, (square G).Adj u v → column v ≤ column u + 2 := by decide

private theorem walkBound {u v : V} (p : (square G).Walk u v) :
    column v ≤ column u + 2 * p.length := by
  induction p with
  | nil => simp
  | cons h _ ih =>
    have step := stepBound _ _ h
    simp only [Walk.length_cons]
    omega

private def sixSteps : (square G).Walk 2 14 :=
  Walk.ofSupport ([2, 4, 6, 8, 10, 12, 14] : List V) (by decide) (by decide)

theorem squareDistance : (square G).dist 2 14 = 6 := by
  have upper := SimpleGraph.dist_le sixSteps
  change (square G).dist 2 14 ≤ 6 at upper
  obtain ⟨p, hp⟩ := sixSteps.reachable.exists_walk_length_eq_dist
  have lower := walkBound p
  change 14 ≤ 2 + 2 * p.length at lower
  omega

theorem leastPairDistance : IsLeast (pairDistances (square G)) 6 := by
  refine ⟨⟨2, 14, by decide, (maxVertices _).2 (.inl rfl), (maxVertices _).2 (.inr rfl),
    squareDistance⟩, ?_⟩
  rintro k ⟨x, y, hne, hx, hy, rfl⟩
  rcases (maxVertices x).1 hx with rfl | rfl <;> rcases (maxVertices y).1 hy with rfl | rfl
  · exact (hne rfl).elim
  · exact squareDistance.ge
  · rw [SimpleGraph.dist_comm]; exact squareDistance.ge
  · exact (hne rfl).elim

theorem conjecture138_false : ¬ Conjecture138 := by
  intro h
  obtain ⟨k, hk, tooLong⟩ := h 19 G connected 6 leastPairDistance
  have cap := longestInducedPath.2 hk
  simp [uniqueFlag, uniqueMaximum] at tooLong
  omega

#print axioms conjecture138_false
end WOWII138
