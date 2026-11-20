import RHImpliesLindelof.Defs

open Complex

namespace Lindelof

theorem lindelof_of_parts (hG : Lindelof.ZetaPolyGrowth) (hS : Lindelof.ZetaSmallRightOfHalf)
    (hI : Lindelof.HalfStripInterpolation) : Lindelof.LindelofHypothesis := by
  intro ε hε
  obtain ⟨A, C₀, hA, hC₀, hG⟩ := hG
  set η : ℝ := min (1 / 4) (ε / (8 * A + 8)) with hη_def
  have h8 : (0 : ℝ) < 8 * A + 8 := by linarith
  have hη_pos : 0 < η := lt_min (by norm_num) (div_pos hε h8)
  have hη_le : η ≤ 1 / 4 := min_le_left _ _
  have hη_le' : η * (8 * A + 8) ≤ ε := by
    have : η ≤ ε / (8 * A + 8) := min_le_right _ _
    rwa [le_div_iff₀ h8] at this
  have hAη : A * η ≤ ε / 8 := by nlinarith
  obtain ⟨C₁, hC₁, hS⟩ := hS (1 / 2 + η) (ε / 2) (by linarith) (by linarith) (by linarith)
  have h3A : (1 : ℝ) ≤ 3 ^ A := Real.one_le_rpow (by norm_num) hA
  set C : ℝ := max C₀ (max C₁ (C₀ * 3 ^ A)) with hC_def
  have hC0 : C₀ ≤ C := le_max_left _ _
  have hC1 : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2 : C₀ * 3 ^ A ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCpos : 0 < C := lt_of_lt_of_le hC₀ hC0
  -- interior growth
  have hgrow : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 + η → 1 ≤ s.im →
      ‖riemannZeta s‖ ≤ C * s.im ^ A := by
    intro s h1 h2 h3
    have h0 : 0 ≤ s.im := by linarith
    have := hG s h1 (by linarith) (by rw [abs_of_nonneg h0]; exact h3)
    rw [abs_of_nonneg h0] at this
    exact this.trans (mul_le_mul_of_nonneg_right hC0 (Real.rpow_nonneg h0 _))
  have hdiff : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 + η → 1 ≤ s.im →
      DifferentiableAt ℂ riemannZeta s := by
    intro s _ h2 _
    apply differentiableAt_riemannZeta
    rintro rfl
    simp at h2
    linarith
  have hleft : ∀ t : ℝ, 1 ≤ t → ‖riemannZeta (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C * t ^ A := by
    intro t ht
    have := hgrow (((1 / 4 : ℝ) : ℂ) + t * I) (by simp) (by simp; linarith) (by simpa using ht)
    simpa using this
  have hright : ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (((1 / 2 + η : ℝ) : ℂ) + t * I)‖ ≤ C * t ^ (ε / 2) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    rcases le_or_gt 3 t with h3 | h3
    · have := hS t h3
      push_cast at this ⊢
      exact this.trans (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg ht0 _))
    · have h1 := hG (((1 / 2 + η : ℝ) : ℂ) + t * I) (by simp; linarith) (by simp; linarith)
        (by simpa [abs_of_nonneg ht0] using ht)
      have him : (((1 / 2 + η : ℝ) : ℂ) + t * I).im = t := by simp
      rw [him, abs_of_nonneg ht0] at h1
      have h2 : t ^ A ≤ 3 ^ A := Real.rpow_le_rpow ht0 h3.le hA
      have h4 : (1 : ℝ) ≤ t ^ (ε / 2) := Real.one_le_rpow ht (by linarith)
      calc ‖riemannZeta (((1 / 2 + η : ℝ) : ℂ) + t * I)‖ ≤ C₀ * t ^ A := h1
        _ ≤ C₀ * 3 ^ A := mul_le_mul_of_nonneg_left h2 hC₀.le
        _ ≤ C := hC2
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * t ^ (ε / 2) := mul_le_mul_of_nonneg_left h4 hCpos.le
  obtain ⟨C', hC', hfin⟩ := hI riemannZeta (1 / 4) (1 / 2 + η) A (ε / 2) A C (by linarith)
    hdiff hgrow hleft hright (1 / 2) (by norm_num) (by linarith)
  have hexp : A + (ε / 2 - A) * (1 / 2 - 1 / 4) / (1 / 2 + η - 1 / 4) ≤ ε := by
    have hd : (0 : ℝ) < 1 / 2 + η - 1 / 4 := by linarith
    have : A + (ε / 2 - A) * (1 / 2 - 1 / 4) / (1 / 2 + η - 1 / 4)
        = (A * (1 / 2 + η - 1 / 4) + (ε / 2 - A) * (1 / 2 - 1 / 4)) / (1 / 2 + η - 1 / 4) := by
      rw [add_div, mul_div_assoc, mul_div_cancel_right₀ _ hd.ne']
    rw [this, div_le_iff₀ hd]
    nlinarith
  refine Asymptotics.IsBigO.of_bound C' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := by linarith
  have h := hfin t ht
  have hcast : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by push_cast; rfl
  rw [hcast] at h
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0 _)]
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht hexp) hC'.le)

end Lindelof

#print axioms Lindelof.lindelof_of_parts
