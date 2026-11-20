import RHImpliesLindelof.Growth
import RHImpliesLindelof.LogZeta
import RHImpliesLindelof.ThreeCircles
import RHImpliesLindelof.Littlewood
import RHImpliesLindelof.HalfStrip
import RHImpliesLindelof.Final

open Complex

/-- Littlewood: the Riemann Hypothesis implies the Lindelöf Hypothesis. -/
theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε :=
  Lindelof.lindelof_of_parts Lindelof.zetaPolyGrowth
    (Lindelof.zetaSmallRightOfHalf (Lindelof.logZetaBound hRH Lindelof.zetaPolyGrowth) Lindelof.threeCircles)
    Lindelof.halfStripInterpolation

/-- The same bound as `t → -∞`, by the symmetry `ζ(conj s) = conj (ζ s)`. -/
theorem lindelof_atBot_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atBot] fun t : ℝ => |t| ^ ε := by
  intro ε hε
  have h := (lindelof_of_riemannHypothesis hRH ε hε).comp_tendsto Filter.tendsto_neg_atBot_atTop
  have h1 : ∀ t : ℝ, ‖riemannZeta (1 / 2 + ((-t : ℝ) : ℂ) * I)‖ =
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ := by
    intro t
    have e : (1 / 2 + ((-t : ℝ) : ℂ) * I) = (starRingEnd ℂ) (1 / 2 + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, riemannZeta_conj, Complex.norm_conj]
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  filter_upwards [hc, Filter.eventually_lt_atBot 0] with t ht ht0
  simp only [Function.comp_apply] at ht
  rw [← h1 t, abs_of_neg ht0]
  exact ht

#print axioms lindelof_of_riemannHypothesis
#print axioms lindelof_atBot_of_riemannHypothesis
