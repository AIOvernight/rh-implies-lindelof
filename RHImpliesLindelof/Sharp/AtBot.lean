import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import RHImpliesLindelof.Sharp.Main

/-!
# Littlewood's sharper bound for `ζ` on the critical line as `t → -∞`, under RH

Assuming the Riemann Hypothesis we prove
`‖ζ(1 / 2 + t * I)‖ ≤ exp (C * log |t| / log (log |t|))` for all sufficiently negative `t`.
This follows from the case `t → +∞`
(`exists_norm_riemannZeta_le_exp_log_div_log_log_of_riemannHypothesis`) and the conjugation
symmetry `riemannZeta_conj`.

## Main results

* `exists_norm_riemannZeta_le_exp_log_div_log_log_atBot_of_riemannHypothesis`: the bound above.
-/

open Complex

/-- **Littlewood's bound on the critical line, as `t → -∞`**. Under the Riemann Hypothesis
there is a constant `C` such that
`‖ζ(1 / 2 + t * I)‖ ≤ exp (C * log |t| / log (log |t|))` for all sufficiently negative `t`. -/
theorem exists_norm_riemannZeta_le_exp_log_div_log_log_atBot_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in Filter.atBot,
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (C * Real.log |t| / Real.log (Real.log |t|)) := by
  obtain ⟨C, hC⟩ := exists_norm_riemannZeta_le_exp_log_div_log_log_of_riemannHypothesis hRH
  refine ⟨C, ?_⟩
  filter_upwards [Filter.tendsto_neg_atBot_atTop.eventually hC, Filter.eventually_lt_atBot 0]
    with t ht ht0
  have e : (1 / 2 + ((-t : ℝ) : ℂ) * I) = (starRingEnd ℂ) (1 / 2 + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [e, riemannZeta_conj, norm_conj] at ht
  rwa [abs_of_neg ht0]
