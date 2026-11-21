import Development.AutomorphicArithmetic.PrimitiveCosets.Imports

open Complex Formalism.HC

private theorem rh_of_right (right : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz ht h1
  refine le_antisymm (le_of_not_gt fun h => right s h h1 hz) (le_of_not_gt fun h => ?_)
  have h0 : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  apply right (1 - s) (by rw [sub_re, one_re]; linarith) (fun e => h0 (sub_eq_self.mp e))
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr h1.symm), completedRiemannZeta_one_sub]
  rw [riemannZeta_def_of_ne_zero h0, div_eq_zero_iff] at hz
  rcases hz with hZ | hΓ
  · rw [hZ, zero_div]
  · obtain ⟨_ | n, hn⟩ := Gammaℝ_eq_zero_iff.mp hΓ
    · exact (h0 (by simpa using hn)).elim
    · exact (ht ⟨n, by rw [hn]; push_cast; ring⟩).elim

namespace RiemannGaussian.AlpogeWindow

/-- A one-sided bound on the principal cyclic level suffices for ordinary RH. -/
theorem rh_of_principal_level_windows {la : ℝ} (hla : 1 < la)
    (hw : ∀ θ : ℝ, 1/2 < θ → θ < 1 →
      HasWindows {x : ℝ | (Level.cyc PChar.one).Gm x ≤ x^θ} la) : RiemannHypothesis := by
  apply rh_of_right
  intro s hs _
  obtain ⟨θ, hθ, h⟩ := exists_between (lt_min hs (by norm_num : (1/2 : ℝ) < 1))
  have h₁ := h.trans_le (min_le_right _ _)
  have hz := UpperTheory.Comparison₂.formB (Level.cyc PChar.one) la hla θ (by linarith) h₁
    (hw θ hθ h₁) PChar.one (Level.mem_cyc _) s (h.trans_le (min_le_left _ _))
  simpa only [PChar.one, DirichletCharacter.LFunction_modOne_eq] using hz

end RiemannGaussian.AlpogeWindow
