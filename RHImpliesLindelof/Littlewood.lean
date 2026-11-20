import RHImpliesLindelof.LogZeta
import RHImpliesLindelof.ThreeCircles

/-!
# Littlewood's bound for `ζ` to the right of the critical line

Assuming the Riemann Hypothesis, we show `ζ(σ + t * I) = O(t ^ ε)` for every fixed
`1 / 2 < σ ≤ 1` and every `ε > 0`. The proof applies Hadamard's three-circles theorem
(`Complex.norm_le_interp_of_mem_sphere`) to the logarithm of `ζ` constructed in
`Lindelof.exists_log_riemannZeta_norm_le`, on three circles centred at `2 + t * I`: this gives
`‖log ζ(σ + t * I)‖ ≤ C * (log t) ^ a` with `a < 1`, which is `≤ ε * log t + O(1)`.

## Main results

* `Lindelof.exists_norm_riemannZeta_le_mul_rpow_of_half_lt`: under RH, for `1 / 2 < σ ≤ 1` and
  `ε > 0` there is `C > 0` with `‖ζ(σ + t * I)‖ ≤ C * t ^ ε` for all `t ≥ 3`.
-/

open Complex

namespace Lindelof

/-- A sublinear power is absorbed by a linear term: for `0 < a < 1` there is `K` such that
`C * L ^ a ≤ ε * L + K` for all `L > 0`. -/
private lemma exists_mul_rpow_le_mul_add {C ε a : ℝ} (hC : 0 < C) (hε : 0 < ε) (ha0 : 0 < a)
    (ha1 : a < 1) :
    ∃ K : ℝ, ∀ L : ℝ, 0 < L → C * L ^ a ≤ ε * L + K := by
  set B : ℝ := (C / ε) ^ (1 / (1 - a)) with hB
  have hBpos : 0 < B := Real.rpow_pos_of_pos (div_pos hC hε) _
  refine ⟨C * B ^ a, fun L hL => ?_⟩
  have h1a : 0 < 1 - a := by linarith
  rcases le_or_gt B L with h | h
  · -- L ≥ B, so L^(1-a) ≥ C/ε
    have h1 : C / ε ≤ L ^ (1 - a) := by
      have := Real.rpow_le_rpow hBpos.le h h1a.le
      have e : B ^ (1 - a) = C / ε := by
        rw [hB, ← Real.rpow_mul (div_pos hC hε).le]
        have : 1 / (1 - a) * (1 - a) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have h2 : C ≤ ε * L ^ (1 - a) := by
      have := mul_le_mul_of_nonneg_left h1 hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    have h3 : L ^ (1 - a) * L ^ a = L := by
      rw [← Real.rpow_add hL]; simp
    have hLa : 0 < L ^ a := Real.rpow_pos_of_pos hL _
    have h4 : C * L ^ a ≤ ε * L := by
      calc C * L ^ a ≤ ε * L ^ (1 - a) * L ^ a := mul_le_mul_of_nonneg_right h2 hLa.le
        _ = ε * L := by rw [mul_assoc, h3]
    have : 0 ≤ C * B ^ a := (mul_pos hC (Real.rpow_pos_of_pos hBpos _)).le
    linarith
  · have h1 : L ^ a ≤ B ^ a := Real.rpow_le_rpow hL.le h.le ha0.le
    have := mul_le_mul_of_nonneg_left h1 hC.le
    have : 0 ≤ ε * L := (mul_pos hε hL).le
    linarith

/-- **Littlewood's bound**. Under the Riemann Hypothesis, for every fixed `1 / 2 < σ ≤ 1` and
every `ε > 0` there is a constant `C > 0` such that `‖ζ(σ + t * I)‖ ≤ C * t ^ ε` for all
`t ≥ 3`. -/
theorem exists_norm_riemannZeta_le_mul_rpow_of_half_lt (hRH : RiemannHypothesis) {σ ε : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ t → ‖riemannZeta (σ + t * I)‖ ≤ C * t ^ ε := by
  set δ : ℝ := (σ - 1 / 2) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 / 4 := by rw [hδ]; linarith
  obtain ⟨C, hC, hg⟩ := exists_log_riemannZeta_norm_le hRH hδ0 hδ1
  -- radii
  have hr12 : (1 / 4 : ℝ) < 2 - σ := by linarith
  have hr23 : 2 - σ < 3 / 2 - 2 * δ := by rw [hδ]; linarith
  have hr3R : 3 / 2 - 2 * δ < 3 / 2 - δ := by linarith
  set a : ℝ := Real.log ((2 - σ) / (1 / 4)) / Real.log ((3 / 2 - 2 * δ) / (1 / 4)) with ha
  have hnum : 0 < Real.log ((2 - σ) / (1 / 4)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have hlt : Real.log ((2 - σ) / (1 / 4)) < Real.log ((3 / 2 - 2 * δ) / (1 / 4)) := by
    apply Real.log_lt_log
    · apply div_pos <;> linarith
    · exact div_lt_div_of_pos_right hr23 (by norm_num)
  have ha0 : 0 < a := div_pos hnum (hnum.trans hlt)
  have ha1 : a < 1 := (div_lt_one (hnum.trans hlt)).2 hlt
  obtain ⟨K, hK⟩ := exists_mul_rpow_le_mul_add hC hε ha0 ha1
  refine ⟨Real.exp K, Real.exp_pos K, fun t ht => ?_⟩
  obtain ⟨g, hgd, hgexp, hg3, hg1⟩ := hg t ht
  have htpos : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hdist : dist ((σ : ℂ) + t * I) (2 + t * I) = 2 - σ := by
    rw [Complex.dist_eq]
    have : (σ : ℂ) + t * I - (2 + t * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hb := norm_le_interp_of_mem_sphere (M₁ := C) (M₃ := C * Real.log t)
    (by norm_num) hr12 hr23 hr3R hgd
    (fun z hz => hg1 z (Metric.sphere_subset_closedBall hz))
    (fun z hz => hg3 z (Metric.sphere_subset_closedBall hz))
    (Metric.mem_sphere.2 hdist)
  rw [← ha] at hb
  have hsimp : C ^ (1 - a) * (C * Real.log t) ^ a = C * Real.log t ^ a := by
    rw [Real.mul_rpow hC.le hlog.le, ← mul_assoc, ← Real.rpow_add hC]
    simp
  rw [hsimp] at hb
  have hmem : (σ : ℂ) + t * I ∈ Metric.ball (2 + t * I : ℂ) (3 / 2 - δ) := by
    rw [Metric.mem_ball, hdist]; linarith
  rw [← hgexp _ hmem, Complex.norm_exp]
  have hre : (g (σ + t * I)).re ≤ ε * Real.log t + K :=
    ((Complex.re_le_norm _).trans hb).trans (hK _ hlog)
  calc Real.exp (g (σ + t * I)).re ≤ Real.exp (ε * Real.log t + K) := Real.exp_le_exp.2 hre
    _ = Real.exp K * t ^ ε := by
      rw [Real.rpow_def_of_pos htpos, Real.exp_add, mul_comm ε, mul_comm]

end Lindelof
