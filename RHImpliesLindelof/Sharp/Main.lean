import Mathlib.Analysis.InnerProductSpace.Calculus
import RHImpliesLindelof.Sharp.LogDerivZeta

/-!
# Littlewood's sharper bound for `ζ` on the critical line, under RH

Assuming the Riemann Hypothesis we prove
`‖ζ(1 / 2 + t * I)‖ ≤ exp (C * log t / log (log t))` for all sufficiently large `t`.

The proof integrates the bound
`-(4 * M * (C / M) ^ (x / 15)) ≤ re (ζ' / ζ) (1 / 2 + x + t * I)`, `M = A * log t`
(`Lindelof.exists_neg_mul_rpow_le_re_deriv_riemannZeta_div`) over `0 < x ≤ 1`: since
`∫ M * (C / M) ^ (x / 15) dx ≤ 15 * M / log (M / C)` and `log (M / C) ≥ log (log t)`, this
bounds `log ‖ζ(1 / 2 + x + t * I)‖` by `log ‖ζ(3 / 2 + t * I)‖ + 60 * M / log (log t)`,
uniformly in `x`. Letting `x → 0` gives the result. See `NOTES.md` in this directory for the
paper proof.

## Main results

* `Complex.hasDerivAt_log_norm`: the derivative of `log ‖γ‖` along a real curve `γ` in `ℂ` is
  `re (γ' / γ)`.
* `exists_norm_riemannZeta_le_exp_log_div_log_log_of_riemannHypothesis`: the bound above.
-/

open Complex Filter Topology

/-- The derivative of `y ↦ log ‖γ y‖` for a differentiable curve `γ : ℝ → ℂ` is
`re (γ' / γ)`. -/
theorem Complex.hasDerivAt_log_norm {γ : ℝ → ℂ} {γ' : ℂ} {x : ℝ} (h : HasDerivAt γ γ' x)
    (h0 : γ x ≠ 0) : HasDerivAt (fun y ↦ Real.log ‖γ y‖) (γ' / γ x).re x := by
  have hn : ‖γ x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h0)
  have h1 := (h.norm_sq.log hn).div_const 2
  have hfun : (fun y ↦ Real.log (‖γ y‖ ^ 2) / 2) = fun y ↦ Real.log ‖γ y‖ := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun] at h1
  refine h1.congr_deriv ?_
  rw [Complex.inner, div_re, mul_re, conj_re, conj_im, normSq_eq_norm_sq]
  have hn' : ‖γ x‖ ^ 2 ≠ 0 := hn
  field_simp
  ring

/-- **Littlewood's bound on the critical line**. Under the Riemann Hypothesis there is a
constant `C` such that `‖ζ(1 / 2 + t * I)‖ ≤ exp (C * log t / log (log t))` for all
sufficiently large `t`. -/
theorem exists_norm_riemannZeta_le_exp_log_div_log_log_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in Filter.atTop,
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (C * Real.log t / Real.log (Real.log t)) := by
  obtain ⟨A, C₁, hC₁, hCA, hF⟩ := Lindelof.exists_neg_mul_rpow_le_re_deriv_riemannZeta_div hRH
  obtain ⟨K₂, hK₂, hζ⟩ := Lindelof.exists_exp_neg_le_norm_riemannZeta
  have hA : 0 < A := hC₁.trans_le hCA
  refine ⟨K₂ + 60 * A, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (100 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  set L : ℝ := Real.log t with hL
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt ht0]
    exact Real.exp_one_lt_three.trans (by linarith)
  have hL0 : 0 < L := by linarith
  set ℓ : ℝ := Real.log L with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos hL1
  have hℓL : ℓ ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  set M : ℝ := A * L with hM
  have hM0 : 0 < M := mul_pos hA hL0
  set q : ℝ := C₁ / M with hq
  have hq0 : 0 < q := div_pos hC₁ hM0
  set κ : ℝ := -Real.log q with hκ
  have hκℓ : ℓ ≤ κ := by
    rw [hκ, hq, ← Real.log_inv, inv_div, hℓ]
    refine Real.log_le_log hL0 ?_
    rw [le_div_iff₀ hC₁, hM]
    nlinarith
  have hκ0 : 0 < κ := hℓ0.trans_le hκℓ
  have hqpow : ∀ x : ℝ, q ^ (x / 15) = Real.exp (-(κ * x / 15)) := by
    intro x
    rw [Real.rpow_def_of_pos hq0, hκ]
    congr 1
    ring
  -- nonvanishing and differentiability to the right of the critical line
  have hpt : ∀ σ : ℝ, 1 / 2 < σ → ((σ : ℂ) + t * I) ≠ 1 ∧ riemannZeta (σ + t * I) ≠ 0 := by
    intro σ hσ
    have h1 : ((σ : ℂ) + t * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    refine ⟨h1, fun h0 ↦ ?_⟩
    have := hRH _ h0 (by
      rintro ⟨n, hn⟩
      have := congrArg Complex.im hn
      simp at this
      linarith) h1
    simp at this
    linarith
  set Φ : ℝ → ℝ := fun σ ↦ Real.log ‖riemannZeta (σ + t * I)‖ -
    60 * M / κ * Real.exp (-(κ * (σ - 1 / 2) / 15)) with hΦ
  have hΦd : ∀ σ : ℝ, 1 / 2 < σ → HasDerivAt Φ
      ((deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)).re +
        4 * M * Real.exp (-(κ * (σ - 1 / 2) / 15))) σ := by
    intro σ hσ
    obtain ⟨h1, h0⟩ := hpt σ hσ
    have hγ : HasDerivAt (fun y : ℝ ↦ riemannZeta (y + t * I))
        (deriv riemannZeta (σ + t * I)) σ :=
      ((differentiableAt_riemannZeta h1).hasDerivAt.comp_add_const (σ : ℂ) (t * I)).comp_ofReal
    have h2 := Complex.hasDerivAt_log_norm hγ h0
    have h3 : HasDerivAt (fun y : ℝ ↦ 60 * M / κ * Real.exp (-(κ * (y - 1 / 2) / 15)))
        (60 * M / κ * (Real.exp (-(κ * (σ - 1 / 2) / 15)) * -(κ * 1 / 15))) σ :=
      ((((hasDerivAt_id σ).sub_const (1 / 2)).const_mul κ).div_const 15).neg.exp.const_mul _
    refine (h2.sub h3).congr_deriv ?_
    field_simp
    ring
  -- bound for every point to the right of the critical line
  have hbound : ∀ y : ℝ, 0 < y → y < 1 →
      ‖riemannZeta ((1 / 2 + y : ℝ) + t * I)‖ ≤ Real.exp ((K₂ + 60 * A) * L / ℓ) := by
    intro y hy0 hy1
    have hmono : MonotoneOn Φ (Set.Icc (1 / 2 + y) (3 / 2)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun σ hσ ↦ (hΦd σ (by linarith [hσ.1])).continuousAt.continuousWithinAt)
        (fun σ hσ ↦ ?_) (fun σ hσ ↦ ?_)
      · rw [interior_Icc] at hσ
        exact (hΦd σ (by linarith [hσ.1])).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hσ
        have hσ' : 1 / 2 < σ := by linarith [hσ.1]
        rw [(hΦd σ hσ').deriv]
        have := hF t ht (σ - 1 / 2) (by linarith) (by linarith [hσ.2])
        rw [hqpow] at this
        have e : (1 / 2 + ((σ - 1 / 2 : ℝ) : ℂ) + t * I) = (σ : ℂ) + t * I := by
          push_cast; ring
        rw [e] at this
        linarith
    have h1 := hmono (Set.left_mem_Icc.2 (by linarith)) (Set.right_mem_Icc.2 (by linarith))
      (by linarith : 1 / 2 + y ≤ (3 / 2 : ℝ))
    simp only [hΦ] at h1
    have h32 : ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ Real.exp K₂ := (hζ _ (by simp)).2
    have h32pos : 0 < ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ :=
      (Real.exp_pos _).trans_le (hζ _ (by simp)).1
    have hlog32 : Real.log ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K₂ := by
      rw [Real.log_le_iff_le_exp h32pos]
      exact h32
    have hcoef : 0 ≤ 60 * M / κ := by positivity
    have he1 : Real.exp (-(κ * (1 / 2 + y - 1 / 2) / 15)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ κ * (1 / 2 + y - 1 / 2) / 15 := by
        have : 0 ≤ κ * y := by positivity
        linarith
      linarith
    have he2 : 0 ≤ 60 * M / κ * Real.exp (-(κ * (3 / 2 - 1 / 2) / 15)) := by positivity
    have he3 : 60 * M / κ * Real.exp (-(κ * (1 / 2 + y - 1 / 2) / 15)) ≤ 60 * M / κ := by
      nlinarith
    have hMκ : 60 * M / κ ≤ 60 * A * (L / ℓ) := by
      rw [hM, ← mul_assoc, mul_div_assoc (60 * A)]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hL0.le hℓ0 hκℓ) (by positivity)
    have hLℓ : 1 ≤ L / ℓ := (one_le_div hℓ0).2 hℓL
    have hfinal : Real.log ‖riemannZeta ((1 / 2 + y : ℝ) + t * I)‖ ≤ (K₂ + 60 * A) * L / ℓ := by
      have : K₂ ≤ K₂ * (L / ℓ) := by nlinarith
      have e : (K₂ + 60 * A) * L / ℓ = K₂ * (L / ℓ) + 60 * A * (L / ℓ) := by ring
      rw [e]
      linarith
    have hpos : 0 < ‖riemannZeta ((1 / 2 + y : ℝ) + t * I)‖ :=
      norm_pos_iff.2 (hpt _ (by linarith)).2
    rwa [Real.log_le_iff_le_exp hpos] at hfinal
  -- let `y → 0`
  have hne : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hcont : ContinuousAt (fun y : ℝ ↦ ‖riemannZeta ((1 / 2 + y : ℝ) + t * I)‖) 0 := by
    have h1 : ContinuousAt riemannZeta (((1 / 2 + (0 : ℝ) : ℝ) : ℂ) + t * I) := by
      have e : (((1 / 2 + (0 : ℝ) : ℝ) : ℂ) + t * I) = 1 / 2 + (t : ℂ) * I := by
        push_cast; ring
      rw [e]
      exact (differentiableAt_riemannZeta hne).continuousAt
    have h2 : ContinuousAt (fun y : ℝ ↦ ((1 / 2 + y : ℝ) : ℂ) + t * I) 0 := by fun_prop
    exact (ContinuousAt.comp (f := fun y : ℝ ↦ ((1 / 2 + y : ℝ) : ℂ) + t * I) h1 h2).norm
  have hlim : Tendsto (fun y : ℝ ↦ ‖riemannZeta ((1 / 2 + y : ℝ) + t * I)‖) (𝓝[>] 0)
      (𝓝 ‖riemannZeta ((1 / 2 + (0 : ℝ) : ℝ) + t * I)‖) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ y : ℝ in 𝓝[>] 0, ‖riemannZeta ((1 / 2 + y : ℝ) + t * I)‖ ≤
      Real.exp ((K₂ + 60 * A) * L / ℓ) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with y hy
    exact hbound y hy.1 hy.2
  have hres := le_of_tendsto hlim hev
  have e : (((1 / 2 + (0 : ℝ) : ℝ) : ℂ) + t * I) = 1 / 2 + (t : ℂ) * I := by
    push_cast; ring
  rwa [e] at hres
