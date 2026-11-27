import Graffiti169

/-!
An independent statement of the spanning-tree conclusion of Graffiti.pc 169.
Evenness is expressed by divisibility, a leaf by a unique neighbor, and the
leaf bound by a comparison for every ordered pair of roots. The singleton
failure is checked directly from adjacency.
-/

namespace Graffiti169Audit

open Finset SimpleGraph
variable {V : Type*} [Fintype V]

/-- Count the vertices at even distance from the root in the input graph. -/
noncomputable def evenPopulation (G : SimpleGraph V) (r : V) : ℕ := by
  classical
  exact (univ.filter fun x => 2 ∣ G.dist r x).card

/-- Count vertices that have exactly one neighbor in the candidate tree. -/
noncomputable def leaves (T : SimpleGraph V) : ℕ := by
  classical
  exact (univ.filter fun x => ∃! y, T.Adj x y).card

private theorem even_agrees (G : SimpleGraph V) (r : V) :
    evenPopulation G r = (Graffiti169.evenSide G r).card := by
  classical
  unfold evenPopulation Graffiti169.evenSide
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, Nat.dvd_iff_mod_eq_zero]
  rw [show G.dist r x = G.dist x r from G.dist_comm]

private theorem leaves_agree (T : SimpleGraph V) :
    leaves T = Graffiti169.leafCount T := by
  classical
  unfold leaves Graffiti169.leafCount
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, degree_eq_one_iff_existsUnique_adj]

/-- One tree works for every pair. Its vertex type is the full vertex type of G. -/
theorem spanning_tree_for_all_roots (G : SimpleGraph V) (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, T.Connected ∧ T.IsAcyclic ∧
        (∀ x y, T.Adj x y → G.Adj x y) ∧
        ∀ r s : V, 1 + evenPopulation G r ≤ leaves T + evenPopulation G s := by
  classical
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨T, hsub, htree, hbound⟩ := Graffiti169.exists_spanning_tree hG
  refine ⟨T, htree.connected, htree.isAcyclic, fun _ _ h => hsub h, ?_⟩
  intro r s
  rw [even_agrees, even_agrees, leaves_agree]
  let e : V → ℕ := fun x => (Graffiti169.evenSide G x).card
  have hmax : e r ≤ univ.sup' univ_nonempty e :=
    le_sup' (f := e) (mem_univ r)
  have hmin : univ.inf' univ_nonempty e ≤ e s :=
    inf'_le (f := e) (mem_univ s)
  change 1 + (univ.sup' univ_nonempty e - univ.inf' univ_nonempty e) ≤ _ at hbound
  change 1 + e r ≤ _ + e s
  omega

/-- Directly exhibit the failure of the pairwise bound on the one-vertex graph. -/
theorem singleton_fails :
    ¬ ∃ T : SimpleGraph Unit, ∀ r s : Unit,
        1 + evenPopulation (⊥ : SimpleGraph Unit) r ≤
          leaves T + evenPopulation (⊥ : SimpleGraph Unit) s := by
  classical
  rintro ⟨T, h⟩
  have zero : leaves T = 0 := by simp [leaves]
  have same := h () ()
  rw [zero, zero_add] at same
  omega

#print axioms Graffiti169Audit.spanning_tree_for_all_roots
#print axioms Graffiti169Audit.singleton_fails

end Graffiti169Audit
