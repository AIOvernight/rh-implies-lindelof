import Mathlib.Analysis.Complex.HasPrimitives
import RHImpliesLindelof.BorelCaratheodory
import RHImpliesLindelof.ThreeCircles

/-!
# A logarithm of a zero-free function on a disc, with explicit bounds

This file is a version of the first two steps of Littlewood's argument (see
`RHImpliesLindelof/General.lean`) in which every constant is tracked. The function `F` is only
considered on one disc `ball c (3 / 2 - δ)`, on which it is zero-free and bounded by `exp M`,
and it is assumed to have a logarithm of norm at most `K` at each point of `ball c (1 / 2)`.
The resulting bounds depend on `δ`, `K`, `M` only, not on `F` or on the centre `c`.

## Main results

* `Lindelof.exists_log_norm_le_of_norm_le_exp`: a holomorphic logarithm `g` of `F` on
  `ball c (3 / 2 - δ)` with `‖g‖ ≤ 3 * (M + K) / δ` on `closedBall c (3 / 2 - 2 * δ)` and
  `‖g‖ ≤ 5 * K + 2` on `closedBall c (1 / 4)`.
* `Lindelof.exists_norm_le_mul_exp_of_ne_zero`: for `1 / 4 < r < 3 / 2 - 2 * δ` and `η > 0`
  there is a constant `C`, depending only on `δ`, `r`, `K`, `η`, such that
  `‖F z‖ ≤ C * exp (η * M)` on `sphere c r`, for all such `F`, `c` and all `M ≥ 1`.
-/

open Complex Metric

namespace Lindelof

/-- Let `F` be holomorphic and zero-free on the disc `ball c (3 / 2 - δ)`, bounded by `exp M`
there, and with a logarithm of norm at most `K` at every point of `ball c (1 / 2)`. Then `F`
has a holomorphic logarithm `g` on `ball c (3 / 2 - δ)` with `‖g‖ ≤ 3 * (M + K) / δ` on the
closed disc of radius `3 / 2 - 2 * δ` and `‖g‖ ≤ 5 * K + 2` on the closed disc of radius
`1 / 4`. -/
theorem exists_log_norm_le_of_norm_le_exp {F : ℂ → ℂ} {c : ℂ} {δ K M : ℝ} (hδ : 0 < δ)
    (hδ4 : δ < 1 / 4) (hM : 0 < M)
    (hd : DifferentiableOn ℂ F (ball c (3 / 2 - δ)))
    (hne : ∀ s ∈ ball c (3 / 2 - δ), F s ≠ 0)
    (hgrow : ∀ s ∈ ball c (3 / 2 - δ), ‖F s‖ ≤ Real.exp M)
    (hlog : ∀ s ∈ ball c (1 / 2), ∃ w : ℂ, exp w = F s ∧ ‖w‖ ≤ K) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c (3 / 2 - δ)) ∧
      (∀ s ∈ ball c (3 / 2 - δ), exp (g s) = F s) ∧
      (∀ s ∈ closedBall c (3 / 2 - 2 * δ), ‖g s‖ ≤ 3 * (M + K) / δ) ∧
      (∀ s ∈ closedBall c (1 / 4), ‖g s‖ ≤ 5 * K + 2) := by
  have hFdiff : ∀ s ∈ ball c (3 / 2 - δ), DifferentiableAt ℂ F s := fun s hs ↦
    hd.differentiableAt (isOpen_ball.mem_nhds hs)
  have hfd : DifferentiableOn ℂ (fun s ↦ deriv F s / F s) (ball c (3 / 2 - δ)) :=
    (hd.deriv isOpen_ball).div hd hne
  have hcB : c ∈ ball c (3 / 2 - δ) := mem_ball_self (by linarith)
  obtain ⟨g₀, hg₀exp, hg₀K⟩ := hlog c (mem_ball_self (by norm_num))
  have hK : 0 ≤ K := (norm_nonneg g₀).trans hg₀K
  obtain ⟨g, hgc, hgd⟩ := hfd.isExactOn_ball.with_val_at c g₀
  -- `F * exp (-g)` is constant
  have hFd : ∀ s ∈ ball c (3 / 2 - δ),
      HasDerivAt (fun s ↦ F s * Complex.exp (-g s)) 0 s := by
    intro s hs
    have h1 := (hFdiff s hs).hasDerivAt
    have h2 : HasDerivAt (fun x ↦ Complex.exp (-g x))
        (Complex.exp (-g s) * -(deriv F s / F s)) s := (hgd s hs).neg.cexp
    have h3 : HasDerivAt (fun x ↦ F x * Complex.exp (-g x))
        (deriv F s * Complex.exp (-g s) +
          F s * (Complex.exp (-g s) * -(deriv F s / F s))) s :=
      h1.mul h2
    have h0 := hne s hs
    refine h3.congr_deriv ?_
    have e : F s * (Complex.exp (-g s) * -(deriv F s / F s))
        = -(deriv F s * Complex.exp (-g s)) := by
      field_simp
    rw [e]; ring
  have hexp : ∀ s ∈ ball c (3 / 2 - δ), Complex.exp (g s) = F s := by
    intro s hs
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c (3 / 2 - δ)).isPreconnected
      (fun x hx ↦ (hFd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hFd x hx).deriv) hs hcB
    rw [hgc, ← hg₀exp, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero] at hconst
    have : F s * Complex.exp (-g s) * Complex.exp (g s) = Complex.exp (g s) := by
      rw [hconst, one_mul]
    rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hgdiff : DifferentiableOn ℂ g (ball c (3 / 2 - δ)) := fun s hs ↦
    (hgd s hs).differentiableAt.differentiableWithinAt
  have hre_le : ∀ s ∈ ball c (3 / 2 - δ), ∀ X : ℝ, ‖F s‖ ≤ Real.exp X → (g s).re ≤ X := by
    intro s hs X hX
    rwa [← hexp s hs, Complex.norm_exp, Real.exp_le_exp] at hX
  refine ⟨g, hgdiff, hexp, ?_, ?_⟩
  · -- outer bound
    intro s hs
    have hbc := borelCaratheodory_closedBall (r := 3 / 2 - 2 * δ) hM hgdiff
      (fun z hz ↦ hre_le z hz M (hgrow z hz)) (by linarith) (by linarith) hs
    rw [hgc] at hbc
    have e1 : (3 / 2 - δ) - (3 / 2 - 2 * δ) = δ := by ring
    rw [e1] at hbc
    refine hbc.trans ?_
    rw [← add_div, div_le_div_iff_of_pos_right hδ]
    have h0 : 0 ≤ ‖g₀‖ := norm_nonneg g₀
    nlinarith [mul_nonneg hM.le hδ.le, mul_nonneg h0 hδ.le]
  · -- inner bound
    intro s hs
    have hsub : ball c (1 / 2) ⊆ ball c (3 / 2 - δ) := ball_subset_ball (by linarith)
    have hre : ∀ z ∈ ball c (1 / 2), (g z).re ≤ K + 1 := by
      intro z hz
      obtain ⟨w, hw, hwK⟩ := hlog z hz
      have hb : ‖F z‖ ≤ Real.exp K := by
        rw [← hw, Complex.norm_exp]
        exact Real.exp_le_exp.mpr ((re_le_norm _).trans hwK)
      have := hre_le z (hsub hz) K hb
      linarith
    have hbc := borelCaratheodory_closedBall (r := 1 / 4) (by positivity) (hgdiff.mono hsub) hre
      (by norm_num) (by norm_num) hs
    rw [hgc] at hbc
    refine hbc.trans ?_
    have e : 2 * (K + 1) * (1 / 4) / (1 / 2 - 1 / 4) + ‖g₀‖ * (1 / 2 + 1 / 4) / (1 / 2 - 1 / 4)
        = 2 * (K + 1) + 3 * ‖g₀‖ := by ring
    rw [e]
    linarith

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

/-- **Littlewood's bound with uniform constants**. Let `0 < δ < 1 / 4`,
`1 / 4 < r < 3 / 2 - 2 * δ`, `K` and `η > 0` be given. There is a constant `C`, depending only
on these four numbers, such that the following holds for every function `F`, every centre `c`
and every `M ≥ 1`: if `F` is holomorphic and zero-free on `ball c (3 / 2 - δ)`, bounded by
`exp M` there, and has a logarithm of norm at most `K` at every point of `ball c (1 / 2)`, then
`‖F z‖ ≤ C * exp (η * M)` for all `z` on the circle of centre `c` and radius `r`. -/
theorem exists_norm_le_mul_exp_of_ne_zero {δ r K η : ℝ} (hδ : 0 < δ) (hδ4 : δ < 1 / 4)
    (hr : 1 / 4 < r) (hrδ : r < 3 / 2 - 2 * δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (M : ℝ), 1 ≤ M →
      DifferentiableOn ℂ F (ball c (3 / 2 - δ)) → (∀ s ∈ ball c (3 / 2 - δ), F s ≠ 0) →
      (∀ s ∈ ball c (3 / 2 - δ), ‖F s‖ ≤ Real.exp M) →
      (∀ s ∈ ball c (1 / 2), ∃ w : ℂ, exp w = F s ∧ ‖w‖ ≤ K) →
      ∀ z ∈ sphere c r, ‖F z‖ ≤ C * Real.exp (η * M) := by
  have hK₁ : 0 ≤ |K| := abs_nonneg K
  set C₁ : ℝ := max (5 * |K| + 2) (3 * (1 + |K|) / δ) with hC₁
  have hC₁pos : 0 < C₁ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hr3R : 3 / 2 - 2 * δ < 3 / 2 - δ := by linarith
  set a : ℝ := Real.log (r / (1 / 4)) / Real.log ((3 / 2 - 2 * δ) / (1 / 4)) with ha
  have hnum : 0 < Real.log (r / (1 / 4)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have hlt : Real.log (r / (1 / 4)) < Real.log ((3 / 2 - 2 * δ) / (1 / 4)) := by
    apply Real.log_lt_log
    · apply div_pos <;> linarith
    · exact div_lt_div_of_pos_right hrδ (by norm_num)
  have ha0 : 0 < a := div_pos hnum (hnum.trans hlt)
  have ha1 : a < 1 := (div_lt_one (hnum.trans hlt)).2 hlt
  obtain ⟨K₂, hK₂⟩ := exists_mul_rpow_le_mul_add hC₁pos hη ha0 ha1
  refine ⟨Real.exp K₂, Real.exp_pos K₂, fun F c M hM hd hne hgrow hlog z hz => ?_⟩
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  obtain ⟨g, hgd, hgexp, hg3, hg1⟩ := exists_log_norm_le_of_norm_le_exp hδ hδ4 hM0 hd hne hgrow
    (fun s hs ↦ (hlog s hs).imp fun w hw ↦ ⟨hw.1, hw.2.trans (le_abs_self K)⟩)
  have hout : 3 * (M + |K|) / δ ≤ C₁ * M := by
    have h1 : 3 * (M + |K|) / δ ≤ 3 * (1 + |K|) / δ * M := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM0.le)
  have hb := norm_le_interp_of_mem_sphere (M₁ := C₁) (M₃ := C₁ * M)
    (by norm_num) hr hrδ hr3R hgd
    (fun w hw => (hg1 w (sphere_subset_closedBall hw)).trans (le_max_left _ _))
    (fun w hw => (hg3 w (sphere_subset_closedBall hw)).trans hout) hz
  rw [← ha] at hb
  have hsimp : C₁ ^ (1 - a) * (C₁ * M) ^ a = C₁ * M ^ a := by
    rw [Real.mul_rpow hC₁pos.le hM0.le, ← mul_assoc, ← Real.rpow_add hC₁pos]
    simp
  rw [hsimp] at hb
  have hmem : z ∈ ball c (3 / 2 - δ) :=
    sphere_subset_closedBall.trans (closedBall_subset_ball (hrδ.trans hr3R)) hz
  rw [← hgexp z hmem, Complex.norm_exp]
  have hre : (g z).re ≤ η * M + K₂ := ((Complex.re_le_norm _).trans hb).trans (hK₂ _ hM0)
  calc Real.exp (g z).re ≤ Real.exp (η * M + K₂) := Real.exp_le_exp.2 hre
    _ = Real.exp K₂ * Real.exp (η * M) := by rw [Real.exp_add, mul_comm]

end Lindelof
