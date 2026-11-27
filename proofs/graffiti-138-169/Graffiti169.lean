import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Lattice.Nat

/-!
# Graffiti.pc conjecture 169 (Written on the Wall II, 8 August 2005)

`graffiti169` proves that a finite connected simple graph with at least two
vertices has a spanning tree with at least one more leaf than the range of
its even-distance counts. A leaf has degree exactly one. `graffiti169_exact`
includes the one-vertex case and characterizes when the inequality holds.
All distances are measured in the original graph.

Fix a root and discard edges joining vertices of the same distance parity.
Every shortest path to the root survives. In a spanning tree of the remaining
graph, the degrees on either side sum to n - 1. If a side has a vertices and
q of them are leaves, then n - 1 ≥ q + 2(a - q), so q ≥ 2a - n + 1.
Use the even side at a root maximizing its size, and the odd side at a root
minimizing the even side. Adding the two inequalities gives the claim.

The problem is entry 169 of Ermelinda DeLaViña’s Written on the Wall II.
The live University of Houston–Downtown catalogue recorded it as open on
24 November 2026. Definition 107 in the same catalogue specifies degree one.
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html

A related prior result is Theorem 3 of DeLaViña and Waller, “Spanning Trees
with Many Leaves and Average Distance”, Electronic Journal of Combinatorics
15 (2008), R33. Applied to a bipartite spanning tree, that theorem also gives
the color-class bound. This file proves that bound directly from degree sums.
Searches of the catalogue, arXiv, Crossref, OpenAlex and public GitHub issues
found no earlier proof explicitly identifying entry 169. This search cannot
establish priority over all published or unpublished work.

Mathlib v4.33.1 (0df444a360eaa60ab8c11dca51a86af692955474), Lean 4.33.1.
In that Mathlib environment run `lake env lean Graffiti169.lean`.
-/

namespace Graffiti169

open Finset SimpleGraph
variable {V : Type*}

/-- Vertices at even graph distance from `r`, including `r` itself. -/
noncomputable def evenSide [Fintype V] (G : SimpleGraph V) (r : V) : Finset V :=
  univ.filter fun v => G.dist v r % 2 = 0

/-- Number of degree-one vertices. -/
noncomputable def leafCount [Fintype V] (T : SimpleGraph V) : ℕ := by
  classical
  exact (univ.filter fun v => T.degree v = 1).card

/-- The largest leaf count over all trees on `V` whose edges belong to `G`. -/
noncomputable def maxLeafCount [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ k = leafCount T}

/-- Keep just the edges that cross between even and odd distance from `r`. -/
private def parityGraph (G : SimpleGraph V) (r : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ G.dist x r % 2 ≠ G.dist y r % 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- Every shortest walk to the root survives deletion of the same-parity edges. -/
private theorem shortest_reaches {G : SimpleGraph V} (hG : G.Connected)
    {v r : V} (p : G.Walk v r) (hp : p.length = G.dist v r) :
    (parityGraph G r).Reachable v r := by
  induction p with
  | nil => exact .rfl
  | @cons x y z h q ih =>
    have upper : G.dist x z ≤ 1 + G.dist y z := by
      simpa [dist_eq_one_iff_adj.mpr h] using
        (hG.dist_triangle (u := x) (v := y) (w := z))
    have lower := G.dist_le q
    simp only [Walk.length_cons] at hp
    have step : G.dist x z = G.dist y z + 1 := by omega
    have edge : (parityGraph G z).Adj x y := ⟨h, by omega⟩
    exact edge.reachable.trans (ih (by omega))

private theorem parity_connected {G : SimpleGraph V} (hG : G.Connected) (r : V) :
    (parityGraph G r).Connected := by
  refine (connected_iff_exists_forall_reachable _).2 ⟨r, fun v => ?_⟩
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v r
  exact (shortest_reaches hG p hp).symm

/-- Counting degrees on one side of a bipartite tree gives a lower bound on its leaves. -/
private theorem side_bound [Fintype V] [Nontrivial V] {T : SimpleGraph V}
    (hT : T.IsTree) (A B : Finset V) (hAB : T.IsBipartiteWith A B) :
    2 * A.card + 1 ≤ Fintype.card V + leafCount T := by
  classical
  have pointwise (v : V) : 2 ≤ T.degree v + (if T.degree v = 1 then 1 else 0) := by
    have pos := hT.connected.preconnected.degree_pos_of_nontrivial v
    split <;> omega
  have count := Finset.sum_le_sum (s := A) (fun v _ => pointwise v)
  simp only [sum_const, smul_eq_mul, sum_add_distrib, ← Finset.card_filter] at count
  have edgeSum := T.isBipartiteWith_sum_degrees_eq_card_edges hAB
  have treeSize := hT.card_edgeFinset
  have subset : (A.filter fun v => T.degree v = 1) ⊆
      (univ.filter fun v => T.degree v = 1) := filter_subset_filter _ (subset_univ _)
  have cardLe : (A.filter fun v => T.degree v = 1).card ≤ leafCount T := card_le_card subset
  omega

private theorem leaf_counts_bounded [Fintype V] (G : SimpleGraph V) :
    BddAbove {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ k = leafCount T} := by
  classical
  refine ⟨Fintype.card V, ?_⟩
  rintro k ⟨S, _, _, rfl⟩
  exact (univ.filter _).card_le_univ

private theorem tree_le_max [Fintype V] {G T : SimpleGraph V} (h : T ≤ G) (hT : T.IsTree) :
    leafCount T ≤ maxLeafCount G :=
  le_csSup (leaf_counts_bounded G) ⟨T, h, hT, rfl⟩

/-- The size of each of the two distance-parity classes obeys the same bound. -/
theorem parity_bounds [Fintype V] [Nontrivial V] {G : SimpleGraph V}
    (hG : G.Connected) (r : V) :
    2 * (evenSide G r).card + 1 ≤ Fintype.card V + maxLeafCount G ∧
    2 * (Fintype.card V - (evenSide G r).card) + 1 ≤ Fintype.card V + maxLeafCount G := by
  classical
  let A := evenSide G r
  obtain ⟨T, hsub, hT⟩ := (parity_connected hG r).exists_isTree_le
  have bip : T.IsBipartiteWith (A : Set V) ((Aᶜ : Finset V) : Set V) := by
    constructor
    · rw [Finset.coe_compl]
      exact disjoint_compl_right
    · intro x y h
      have opposite := (hsub h).2
      simp only [A, evenSide, coe_compl, Set.mem_compl_iff, mem_coe, mem_filter, mem_univ, true_and]
      omega
  have inside := side_bound hT A Aᶜ bip
  have outside := side_bound hT Aᶜ A bip.symm
  have maxBound := tree_le_max (G := G) (T := T) (fun _ _ h => (hsub h).1) hT
  rw [Finset.card_compl] at outside
  change 2 * A.card + 1 ≤ _ ∧ 2 * (Fintype.card V - A.card) + 1 ≤ _
  omega

/-- An equivalent form of Conjecture 169 for any ordered pair of roots. -/
theorem two_roots [Fintype V] [Nontrivial V] {G : SimpleGraph V}
    (hG : G.Connected) (u v : V) :
    1 + (evenSide G u).card ≤ maxLeafCount G + (evenSide G v).card := by
  have first := (parity_bounds hG u).1
  have second := (parity_bounds hG v).2
  have size := (evenSide G v).card_le_univ
  omega

/-- The original maximum-minus-minimum inequality for finite connected simple graphs
with at least two vertices. -/
theorem graffiti169 [Fintype V] [Nontrivial V] {G : SimpleGraph V} (hG : G.Connected) :
    1 + ((univ.sup' univ_nonempty fun r => (evenSide G r).card) -
         (univ.inf' univ_nonempty fun r => (evenSide G r).card)) ≤ maxLeafCount G := by
  classical
  let e := fun r => (evenSide G r).card
  obtain ⟨u, hu, hmax⟩ := univ.exists_mem_eq_sup' univ_nonempty e
  obtain ⟨v, hv, hmin⟩ := univ.exists_mem_eq_inf' univ_nonempty e
  change 1 + (univ.sup' univ_nonempty e - univ.inf' univ_nonempty e) ≤ _
  have order : e v ≤ e u := hmax ▸ le_sup' (f := e) hv
  have bound : 1 + e u ≤ maxLeafCount G + e v := two_roots hG u v
  rw [hmax, hmin]
  omega

/-- The bound is attained or exceeded by an actual spanning tree of `G`. -/
theorem exists_spanning_tree [Fintype V] [Nontrivial V] {G : SimpleGraph V}
    (hG : G.Connected) : ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
    1 + ((univ.sup' univ_nonempty fun r => (evenSide G r).card) -
         (univ.inf' univ_nonempty fun r => (evenSide G r).card)) ≤ leafCount T := by
  obtain ⟨S, hS, hTree⟩ := hG.exists_isTree_le
  have hne : ({k : ℕ | ∃ T : SimpleGraph V,
      T ≤ G ∧ T.IsTree ∧ k = leafCount T} : Set ℕ).Nonempty :=
    ⟨leafCount S, S, hS, hTree, rfl⟩
  obtain ⟨T, hT, isTree, hmax⟩ := Nat.sSup_mem hne (leaf_counts_bounded G)
  exact ⟨T, hT, isTree, (graffiti169 hG).trans_eq hmax⟩

/-- A graph on one vertex has no degree-one vertices in any spanning tree. -/
private theorem maxLeafCount_subsingleton [Fintype V] [Subsingleton V]
    {G : SimpleGraph V} (hG : G.Connected) : maxLeafCount G = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold maxLeafCount
  apply csSup_le
  · obtain ⟨T, h, hT⟩ := hG.exists_isTree_le
    exact ⟨leafCount T, T, h, hT, rfl⟩
  · rintro k ⟨T, _, _, rfl⟩
    have hbot : T = ⊥ := by
      ext x y
      rw [Subsingleton.elim y x]
      simp
    subst T
    simp [leafCount]

/-- Complete classification, including the one-vertex exception under the
catalogue's degree-one definition of a leaf. -/
theorem graffiti169_exact [Fintype V] [Nonempty V] {G : SimpleGraph V} (hG : G.Connected) :
    (1 + ((univ.sup' univ_nonempty fun r => (evenSide G r).card) -
          (univ.inf' univ_nonempty fun r => (evenSide G r).card)) ≤ maxLeafCount G) ↔
      1 < Fintype.card V := by
  classical
  rcases subsingleton_or_nontrivial V with h | h
  · let _ : Subsingleton V := h
    have size : Fintype.card V ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr h
    rw [maxLeafCount_subsingleton hG]
    omega
  · let _ : Nontrivial V := h
    exact iff_of_true (graffiti169 hG) (Fintype.one_lt_card_iff_nontrivial.mpr h)

#print axioms Graffiti169.graffiti169
#print axioms Graffiti169.graffiti169_exact
#print axioms Graffiti169.exists_spanning_tree

end Graffiti169
