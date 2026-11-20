import RHImpliesLindelof.Defs

open Complex Set Metric

namespace Lindelof

theorem threeCircles : ThreeCircles := by
  intro g c r₁ r₂ r₃ R M₁ M₃ hr₁ h12 h23 h3R hM₁ hM₃ hg hb₁ hb₃ z hz
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hr₃ : 0 < r₃ := hr₂.trans h23
  set F : ℂ → ℂ := fun w => g (c + exp w) with hF
  have hlu : Real.log r₁ < Real.log r₃ := Real.log_lt_log hr₁ (h12.trans h23)
  have hnorm : ∀ w : ℂ, dist (c + exp w) c = Real.exp w.re := by
    intro w
    rw [dist_eq_norm, add_sub_cancel_left, norm_exp]
  -- membership in the ball
  have hmem : ∀ w : ℂ, w.re ≤ Real.log r₃ → c + exp w ∈ ball c R := by
    intro w hw
    rw [mem_ball, hnorm]
    calc Real.exp w.re ≤ Real.exp (Real.log r₃) := Real.exp_le_exp.mpr hw
      _ = r₃ := Real.exp_log hr₃
      _ < R := h3R
  have hdiff : DifferentiableOn ℂ F (HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃)) := by
    intro w hw
    have hw' : w.re ≤ Real.log r₃ := hw.2
    have h1 : DifferentiableAt ℂ g (c + exp w) :=
      hg.differentiableAt (isOpen_ball.mem_nhds (hmem w hw'))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => c + exp w) w :=
      (differentiableAt_const c).add differentiableAt_exp
    exact (h1.comp w h2).differentiableWithinAt
  have hclosed : IsClosed (HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃)) :=
    isClosed_Icc.preimage continuous_re
  have hsub : closure (HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) ⊆
      HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃) :=
    hclosed.closure_subset_iff.mpr (fun w hw => ⟨hw.1.le, hw.2.le⟩)
  have hd : DiffContOnCl ℂ F (HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) :=
    (hdiff.mono hsub).diffContOnCl
  -- boundedness
  have hcont : ContinuousOn g (closedBall c r₃) :=
    hg.continuousOn.mono (closedBall_subset_ball h3R)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r₃).exists_bound_of_continuousOn hcont
  have hB : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    apply hC
    rw [mem_closedBall, hnorm]
    calc Real.exp w.re ≤ Real.exp (Real.log r₃) := Real.exp_le_exp.mpr hw.2
      _ = r₃ := Real.exp_log hr₃
  have ha : ∀ w ∈ re ⁻¹' {Real.log r₁}, ‖F w‖ ≤ M₁ := by
    intro w hw
    apply hb₁
    rw [hnorm, show w.re = Real.log r₁ from hw, Real.exp_log hr₁]
  have hb : ∀ w ∈ re ⁻¹' {Real.log r₃}, ‖F w‖ ≤ M₃ := by
    intro w hw
    apply hb₃
    rw [hnorm, show w.re = Real.log r₃ from hw, Real.exp_log hr₃]
  -- the point
  have hzc : z - c ≠ 0 := by
    intro h
    rw [dist_eq_norm, h, norm_zero] at hz
    exact hr₂.ne hz
  have hre : (log (z - c)).re = Real.log r₂ := by
    rw [log_re, ← dist_eq_norm, hz]
  have hFz : F (log (z - c)) = g z := by
    simp only [hF, exp_log hzc, add_sub_cancel]
  have hmemz : log (z - c) ∈ HadamardThreeLines.verticalClosedStrip (Real.log r₁) (Real.log r₃) :=
    ⟨by rw [hre]; exact (Real.log_lt_log hr₁ h12).le,
     by rw [hre]; exact (Real.log_lt_log hr₂ h23).le⟩
  have key := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hmemz hd hB ha hb
  rw [hFz, hre, ← Real.log_div hr₂.ne' hr₁.ne', ← Real.log_div hr₃.ne' hr₁.ne'] at key
  exact key

end Lindelof

#print axioms Lindelof.threeCircles
