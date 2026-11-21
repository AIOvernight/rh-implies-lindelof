import RHImpliesLindelof.Sharp.Main

/-!
# Littlewood's sharper bound on the critical line: abstract version

Let `F : ℂ → ℂ` be a function which, in the region `1 ≤ im s`,

* is holomorphic on `1 / 4 < re s`,
* satisfies `‖F s‖ ≤ C₀ * (im s) ^ A` in the strip `1 / 4 ≤ re s ≤ 4`,
* does not vanish on `1 / 2 < re s`,
* satisfies `exp (-K₂) ≤ ‖F s‖ ≤ exp K₂` on `3 / 2 ≤ re s`.

Then `‖F (1 / 2 + t * I)‖ ≤ exp (C * log t / log (log t))` for all `t ≥ 100`. This is the
argument of `RHImpliesLindelof/Sharp/LogDerivZeta.lean` and `RHImpliesLindelof/Sharp/Main.lean`
(see `NOTES.md` in this directory) with `ζ` replaced by `F`; it applies to Dirichlet
`L`-functions, see `RHImpliesLindelof/Sharp/DirichletMain.lean`.

## Main results

* `Lindelof.exists_norm_deriv_div_le_of_exp_neg_le_norm`: `‖F' / F‖ ≤ C` on `7 / 4 ≤ re s`,
  `2 ≤ im s`.
* `Lindelof.exists_neg_mul_log_le_re_deriv_div_of_ne_zero`: `-(A₁ * log (im s)) ≤ re (F' / F)`
  for `1 / 2 < re s ≤ 5 / 2` and `3 ≤ im s`, from the one-sided Landau lemma
  `Complex.exists_neg_mul_log_le_re_deriv_div`.
* `Lindelof.exists_neg_mul_rpow_le_re_deriv_div_of_ne_zero`: there are `0 < C ≤ A₀` such that
  for `t ≥ 100` and `0 < x ≤ 1`, with `M = A₀ * log t`,
  `-(4 * M * (C / M) ^ (x / 15)) ≤ re (F' / F) (1 / 2 + x + t * I)`.
* `Lindelof.exists_norm_le_exp_log_div_log_log_of_ne_zero`: the bound on the critical line.
-/

open Complex Metric Filter Topology

namespace Lindelof

variable {F : ℂ → ℂ} {A C₀ K₂ : ℝ}

/-- If `F` is holomorphic on `1 / 4 < re s`, `1 ≤ im s` and `exp (-K₂) ≤ ‖F s‖ ≤ exp K₂` on
`3 / 2 ≤ re s`, `1 ≤ im s`, then `F' / F` is bounded on `7 / 4 ≤ re s`, `2 ≤ im s`. -/
theorem exists_norm_deriv_div_le_of_exp_neg_le_norm
    (hd : ∀ s : ℂ, 1 / 4 < s.re → 1 ≤ s.im → DifferentiableAt ℂ F s)
    (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → 1 ≤ s.im →
      Real.exp (-K₂) ≤ ‖F s‖ ∧ ‖F s‖ ≤ Real.exp K₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 7 / 4 ≤ s.re → 2 ≤ s.im → ‖deriv F s / F s‖ ≤ C := by
  refine ⟨Real.exp K₂ / (1 / 4) / Real.exp (-K₂), by positivity, fun s hs him ↦ ?_⟩
  have hre : ∀ w ∈ closedBall s (1 / 4), 3 / 2 ≤ w.re ∧ 1 ≤ w.im := by
    intro w hw
    have h1 := abs_re_le_norm (w - s)
    have h2 := abs_im_le_norm (w - s)
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [sub_re, abs_le] at h1
    rw [sub_im, abs_le] at h2
    constructor <;> linarith
  have hdo : DifferentiableOn ℂ F {w : ℂ | 1 / 4 < w.re ∧ 1 ≤ w.im} := fun w hw ↦
    (hd w hw.1 hw.2).differentiableWithinAt
  have hsub : closedBall s (1 / 4) ⊆ {w : ℂ | 1 / 4 < w.re ∧ 1 ≤ w.im} := fun w hw ↦ by
    obtain ⟨h1, h2⟩ := hre w hw
    exact ⟨by linarith, h2⟩
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 4)
    (hdo.diffContOnCl_ball hsub)
    (fun w hw ↦ (hK w (hre w (sphere_subset_closedBall hw)).1
      (hre w (sphere_subset_closedBall hw)).2).2)
  have hlow := (hK s (by linarith) (by linarith)).1
  rw [norm_div]
  exact div_le_div₀ (by positivity) hcauchy (Real.exp_pos _) hlow

/-- If `F` is holomorphic, of polynomial growth, zero-free to the right of the critical line
and bounded above and below on `3 / 2 ≤ re s` (all in the region `1 ≤ im s`), then
`re (F' / F)` is bounded below by `-(A₁ * log (im s))` in the strip `1 / 2 < re s ≤ 5 / 2`,
`3 ≤ im s`. -/
theorem exists_neg_mul_log_le_re_deriv_div_of_ne_zero (hA : 0 ≤ A) (hC₀ : 0 < C₀)
    (hd : ∀ s : ℂ, 1 / 4 < s.re → 1 ≤ s.im → DifferentiableAt ℂ F s)
    (hG : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ s.im → ‖F s‖ ≤ C₀ * s.im ^ A)
    (hne : ∀ s : ℂ, 1 / 2 < s.re → 1 ≤ s.im → F s ≠ 0)
    (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → 1 ≤ s.im →
      Real.exp (-K₂) ≤ ‖F s‖ ∧ ‖F s‖ ≤ Real.exp K₂) :
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 5 / 2 → 3 ≤ s.im →
      -(A₁ * Real.log s.im) ≤ (deriv F s / F s).re := by
  have hK₂ : 0 ≤ K₂ := by
    obtain ⟨h1, h2⟩ := hK (3 / 2 + I) (by simp) (by simp)
    have := Real.exp_le_exp.1 (h1.trans h2)
    linarith
  obtain ⟨K, hK0, hL⟩ := Complex.exists_neg_mul_log_le_re_deriv_div (r₁ := 1) (r₂ := 17 / 16)
    (r := 9 / 8) (R := 5 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨K * (|Real.log C₀| + 2 * A + K₂), by positivity, fun s hs1 hs2 hs3 ↦ ?_⟩
  set τ : ℝ := s.im with hτ
  set c : ℂ := 3 / 2 + τ * I with hc
  have hcre : c.re = 3 / 2 := by simp [hc]
  have hcim : c.im = τ := by simp [hc]
  have hgeo : ∀ {ρ : ℝ} {w : ℂ}, dist w c ≤ ρ → |w.re - 3 / 2| ≤ ρ ∧ |w.im - τ| ≤ ρ := by
    intro ρ w hw
    rw [dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - c)
    have h2 := abs_im_le_norm (w - c)
    rw [sub_re, hcre] at h1
    rw [sub_im, hcim] at h2
    exact ⟨h1.trans hw, h2.trans hw⟩
  have hτpos : 0 < τ := by linarith
  have hdiff : DifferentiableOn ℂ F (ball c (5 / 4)) := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - c)
    have h2 := abs_im_le_norm (w - c)
    rw [sub_re, hcre, abs_le] at h1
    rw [sub_im, hcim, abs_le] at h2
    exact (hd w (by linarith) (by linarith)).differentiableWithinAt
  have hB : ∀ w ∈ closedBall c (9 / 8), ‖F w‖ ≤ C₀ * (τ + 2) ^ A := by
    intro w hw
    obtain ⟨h1, h2⟩ := hgeo (mem_closedBall.1 hw)
    rw [abs_le] at h1 h2
    refine (hG w (by linarith) (by linarith) (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) (by linarith) hA) hC₀.le
  have hcF := (hK c (by rw [hcre]) (by rw [hcim]; linarith)).1
  have hc0 : F c ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le hcF)
  have hzero : ∀ ρ ∈ closedBall c (17 / 16), F ρ = 0 → ρ.re ≤ 1 / 2 := by
    intro ρ hρ h0
    obtain ⟨-, h2⟩ := hgeo (mem_closedBall.1 hρ)
    rw [abs_le] at h2
    by_contra hlt
    exact hne ρ (not_le.1 hlt) (by linarith) h0
  have hsc : s ∈ closedBall c 1 := by
    rw [mem_closedBall, dist_eq_norm]
    have : s - c = ((s.re - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc, hτ]
    rw [this, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have key := hL F c (1 / 2) (C₀ * (τ + 2) ^ A) hdiff hB hc0 hzero s hsc hs1
  refine le_trans ?_ key
  have hlogτ : 1 ≤ Real.log τ := by
    rw [Real.le_log_iff_exp_le hτpos]
    exact Real.exp_one_lt_three.le.trans hs3
  have hcpos : 0 < ‖F c‖ := norm_pos_iff.2 hc0
  have hτA : 0 < (τ ^ 2) ^ A := Real.rpow_pos_of_pos (by positivity) _
  have h1 : Real.log (C₀ * (τ + 2) ^ A / ‖F c‖) ≤
      (|Real.log C₀| + 2 * A + K₂) * Real.log τ := by
    have hB0 : 0 < C₀ * (τ + 2) ^ A :=
      mul_pos hC₀ (Real.rpow_pos_of_pos (by linarith) _)
    calc Real.log (C₀ * (τ + 2) ^ A / ‖F c‖)
        ≤ Real.log (C₀ * (τ ^ 2) ^ A * Real.exp K₂) := by
          refine Real.log_le_log (div_pos hB0 hcpos) ?_
          rw [div_le_iff₀ hcpos]
          have h3 : (1 : ℝ) ≤ Real.exp K₂ * ‖F c‖ := by
            calc (1 : ℝ) = Real.exp K₂ * Real.exp (-K₂) := by
                  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
              _ ≤ Real.exp K₂ * ‖F c‖ :=
                  mul_le_mul_of_nonneg_left hcF (Real.exp_pos _).le
          have h4 : C₀ * (τ + 2) ^ A ≤ C₀ * (τ ^ 2) ^ A :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by linarith) (by nlinarith) hA) hC₀.le
          calc C₀ * (τ + 2) ^ A ≤ C₀ * (τ ^ 2) ^ A * 1 := by linarith
            _ ≤ C₀ * (τ ^ 2) ^ A * (Real.exp K₂ * ‖F c‖) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = C₀ * (τ ^ 2) ^ A * Real.exp K₂ * ‖F c‖ := by ring
      _ = Real.log C₀ + 2 * A * Real.log τ + K₂ := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
            Real.log_mul hC₀.ne' hτA.ne', Real.log_rpow (by positivity), Real.log_pow,
            Real.log_exp]
          push_cast; ring
      _ ≤ (|Real.log C₀| + 2 * A + K₂) * Real.log τ := by
          have h5 := mul_le_mul_of_nonneg_left hlogτ (abs_nonneg (Real.log C₀))
          have h6 := mul_le_mul_of_nonneg_left hlogτ hK₂
          have h7 := le_abs_self (Real.log C₀)
          linarith
  have := mul_le_mul_of_nonneg_left h1 hK0
  rw [mul_assoc]
  linarith

/-- If `-M ≤ re z` with `M > 0`, then `‖z‖ ≤ ‖z + 2 * M‖`. -/
private lemma norm_le_norm_add_two_mul' {z : ℂ} {M : ℝ} (hM : 0 < M) (hz : -M ≤ z.re) :
    ‖z‖ ≤ ‖z + 2 * (M : ℂ)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im]
  nlinarith

/-- Under the hypotheses of `Lindelof.exists_neg_mul_log_le_re_deriv_div_of_ne_zero`,
`re (F' / F) (1 / 2 + x + t * I)` is bounded below by `-(4 * M * (C / M) ^ (x / 15))` with
`M = A₀ * log t`, uniformly for `0 < x ≤ 1` and `t ≥ 100`. -/
theorem exists_neg_mul_rpow_le_re_deriv_div_of_ne_zero (hA : 0 ≤ A) (hC₀ : 0 < C₀)
    (hd : ∀ s : ℂ, 1 / 4 < s.re → 1 ≤ s.im → DifferentiableAt ℂ F s)
    (hG : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ s.im → ‖F s‖ ≤ C₀ * s.im ^ A)
    (hne : ∀ s : ℂ, 1 / 2 < s.re → 1 ≤ s.im → F s ≠ 0)
    (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → 1 ≤ s.im →
      Real.exp (-K₂) ≤ ‖F s‖ ∧ ‖F s‖ ≤ Real.exp K₂) :
    ∃ A₀ C : ℝ, 0 < C ∧ C ≤ A₀ ∧ ∀ t : ℝ, 100 ≤ t → ∀ x : ℝ, 0 < x → x ≤ 1 →
      -(4 * (A₀ * Real.log t) * (C / (A₀ * Real.log t)) ^ (x / 15)) ≤
        (deriv F (1 / 2 + x + t * I) / F (1 / 2 + x + t * I)).re := by
  obtain ⟨A₁, hA₁, hlow⟩ := exists_neg_mul_log_le_re_deriv_div_of_ne_zero hA hC₀ hd hG hne hK
  obtain ⟨C, hC, hbdd⟩ := exists_norm_deriv_div_le_of_exp_neg_le_norm hd hK
  refine ⟨2 * A₁ + C, C, hC, by linarith, fun t ht x hx0 hx1 ↦ ?_⟩
  have ht0 : 0 < t := by linarith
  have hlog : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  set M : ℝ := (2 * A₁ + C) * Real.log t with hM
  have hMC : C ≤ M := by rw [hM]; nlinarith
  have hMA : 2 * A₁ * Real.log t ≤ M := by rw [hM]; nlinarith
  have hMpos : 0 < M := hC.trans_le hMC
  set G : ℂ → ℂ := fun s ↦ deriv F s / F s with hGdef
  set c : ℂ := 2 + t * I with hc
  have hgeo : ∀ {ρ : ℝ} {w : ℂ}, dist w c ≤ ρ → |w.re - 2| ≤ ρ ∧ |w.im - t| ≤ ρ := by
    intro ρ w hw
    rw [dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - c)
    have h2 := abs_im_le_norm (w - c)
    simp only [hc, sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_im, add_im,
      mul_im, re_ofNat, im_ofNat] at h1 h2
    simp only [mul_zero, mul_one, sub_zero, zero_add, add_zero] at h1 h2
    exact ⟨h1.trans hw, h2.trans hw⟩
  have hre : ∀ w ∈ ball c (3 / 2), 1 / 2 < w.re ∧ w.re < 7 / 2 ∧ 98 ≤ w.im := by
    intro w hw
    have h2 := (hgeo (mem_ball.1 hw).le).2
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - c)
    simp only [hc, sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, re_ofNat] at h1
    simp only [mul_zero, mul_one, sub_zero, add_zero] at h1
    have := h1.trans_lt hw
    rw [abs_lt] at this
    rw [abs_le] at h2
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  have hne0 : ∀ w ∈ ball c (3 / 2), F w ≠ 0 := fun w hw ↦
    hne w (hre w hw).1 (by linarith [(hre w hw).2.2])
  have hFd' : DifferentiableOn ℂ F (ball c (3 / 2)) := fun w hw ↦
    (hd w (by linarith [(hre w hw).1]) (by linarith [(hre w hw).2.2])).differentiableWithinAt
  have hGd : DifferentiableOn ℂ G (ball c (3 / 2)) := (hFd'.deriv isOpen_ball).div hFd' hne0
  -- lower bound for `re G` on the whole disc
  have hGre : ∀ w ∈ ball c (3 / 2), -M ≤ (G w).re := by
    intro w hw
    obtain ⟨hw1, -, hw3⟩ := hre w hw
    rcases le_total w.re (5 / 2) with h | h
    · have h2 := (hgeo (mem_ball.1 hw).le).2
      rw [abs_le] at h2
      have h3 := hlow w hw1 h (by linarith)
      have h4 : Real.log w.im ≤ 2 * Real.log t := by
        rw [← Real.log_rpow ht0]
        refine Real.log_le_log (by linarith) ?_
        rw [Real.rpow_two]
        nlinarith
      have h5 : A₁ * Real.log w.im ≤ M := by
        have := mul_le_mul_of_nonneg_left h4 hA₁
        linarith
      linarith
    · have h3 := hbdd w (by linarith) (by linarith)
      have h4 := abs_re_le_norm (G w)
      rw [abs_le] at h4
      have : ‖G w‖ ≤ M := h3.trans hMC
      linarith
  have hden : ∀ w ∈ ball c (3 / 2), G w + 2 * (M : ℂ) ≠ 0 := by
    intro w hw h0
    have := congrArg Complex.re h0
    simp only [add_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, zero_re] at this
    linarith [hGre w hw]
  set H : ℂ → ℂ := fun w ↦ G w / (G w + 2 * (M : ℂ)) with hH
  have hHd : DifferentiableOn ℂ H (ball c (3 / 2)) :=
    hGd.div (hGd.add_const _) hden
  have hH1 : ∀ w ∈ ball c (3 / 2), ‖H w‖ ≤ 1 := by
    intro w hw
    rw [hH, norm_div]
    exact div_le_one_of_le₀ (norm_le_norm_add_two_mul' hMpos (hGre w hw)) (norm_nonneg _)
  set q : ℝ := C / M with hq
  have hq0 : 0 < q := div_pos hC hMpos
  have hq1 : q ≤ 1 := (div_le_one hMpos).2 hMC
  have hHq : ∀ w ∈ sphere c (1 / 4), ‖H w‖ ≤ q := by
    intro w hw
    have hwB : w ∈ ball c (3 / 2) := by
      rw [mem_sphere] at hw; rw [mem_ball, hw]; norm_num
    have h1 := (hgeo (mem_sphere.1 hw).le).1
    rw [abs_le] at h1
    have h3 : ‖G w‖ ≤ C := hbdd w (by linarith) (by linarith [(hre w hwB).2.2])
    have h4 : M ≤ ‖G w + 2 * (M : ℂ)‖ := by
      have h5 := Complex.re_le_norm (G w + 2 * (M : ℂ))
      simp only [add_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im] at h5
      have h6 := abs_re_le_norm (G w)
      rw [abs_le] at h6
      linarith
    rw [hH, norm_div, hq]
    exact div_le_div₀ hC.le h3 hMpos h4
  -- three circles
  set z : ℂ := 1 / 2 + x + t * I with hz
  have hdist : dist z c = 3 / 2 - x := by
    rw [dist_eq_norm]
    have : z - c = ((x - 3 / 2 : ℝ) : ℂ) := by
      simp only [hz, hc]; push_cast; ring
    rw [this, norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hzB : z ∈ ball c (3 / 2) := by rw [mem_ball, hdist]; linarith
  have h12 : (1 / 4 : ℝ) < 3 / 2 - x := by linarith
  have h23 : 3 / 2 - x < 3 / 2 - x / 2 := by linarith
  have h3R : 3 / 2 - x / 2 < (3 / 2 : ℝ) := by linarith
  have h3c := norm_le_interp_of_mem_sphere (M₁ := q) (M₃ := 1) (by norm_num) h12 h23 h3R hHd
    hHq (fun w hw ↦ hH1 w (by rw [mem_sphere] at hw; rw [mem_ball, hw]; exact h3R))
    (mem_sphere.2 hdist)
  rw [Real.one_rpow, mul_one] at h3c
  -- the exponent
  have hr₂ : 0 < 3 / 2 - x := by linarith
  have hr₃ : 0 < 3 / 2 - x / 2 := by linarith
  have hl3 : Real.log ((3 / 2 - x / 2) / (1 / 4)) ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (div_pos hr₃ (by norm_num : (0 : ℝ) < 1 / 4))
    have e : (3 / 2 - x / 2) / (1 / 4) = 6 - 2 * x := by ring
    rw [e] at this ⊢
    linarith
  have hl3pos : 0 < Real.log ((3 / 2 - x / 2) / (1 / 4)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have hl2 : x / 3 ≤ Real.log ((3 / 2 - x / 2) / (1 / 4)) - Real.log ((3 / 2 - x) / (1 / 4)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have e : (3 / 2 - x / 2) / (1 / 4) / ((3 / 2 - x) / (1 / 4)) =
        (3 / 2 - x / 2) / (3 / 2 - x) := by
      field_simp
    rw [e]
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hr₃ hr₂)
    refine le_trans ?_ h1
    rw [inv_div, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hr₃]
    have : (1 - x / 3) * (3 / 2 - x / 2) = 3 / 2 - x + x ^ 2 / 6 := by ring
    rw [this]
    nlinarith [sq_nonneg x]
  have hexp : x / 15 ≤ 1 - Real.log ((3 / 2 - x) / (1 / 4)) /
      Real.log ((3 / 2 - x / 2) / (1 / 4)) := by
    rw [one_sub_div hl3pos.ne', le_div_iff₀ hl3pos]
    nlinarith
  have hHz : ‖H z‖ ≤ q ^ (x / 15) :=
    h3c.trans (Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hexp)
  -- back from `H` to `G`
  have hqx : 0 < q ^ (x / 15) := Real.rpow_pos_of_pos hq0 _
  change -(4 * M * q ^ (x / 15)) ≤ (G z).re
  rcases le_or_gt (q ^ (x / 15)) (1 / 2) with hsmall | hbig
  · have hHhalf : ‖H z‖ ≤ 1 / 2 := hHz.trans hsmall
    have hrel : G z * (1 - H z) = 2 * (M : ℂ) * H z := by
      have hd := hden z hzB
      simp only [hH]
      field_simp
      ring
    have h1 := congrArg norm hrel
    rw [norm_mul, norm_mul, norm_mul, norm_ofNat, norm_real, Real.norm_of_nonneg hMpos.le] at h1
    have h2 : 1 - ‖H z‖ ≤ ‖1 - H z‖ := by
      have := norm_sub_norm_le (1 : ℂ) (H z)
      rwa [norm_one] at this
    have h3 : ‖G z‖ * (1 / 2) ≤ 2 * M * ‖H z‖ := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h4 : 2 * M * ‖H z‖ ≤ 2 * M * q ^ (x / 15) :=
      mul_le_mul_of_nonneg_left hHz (by positivity)
    have h5 := abs_re_le_norm (G z)
    rw [abs_le] at h5
    linarith
  · have := hGre z hzB
    nlinarith

/-- **Littlewood's bound on the critical line, abstract version**. Let `F` be a function
that, in the region `1 ≤ im s`, is holomorphic on `1 / 4 < re s`, of polynomial growth in the
strip `1 / 4 ≤ re s ≤ 4`, zero-free on `1 / 2 < re s`, and bounded above and below on
`3 / 2 ≤ re s`. Then there is a constant `C` such that
`‖F (1 / 2 + t * I)‖ ≤ exp (C * log t / log (log t))` for all `t ≥ 100`. -/
theorem exists_norm_le_exp_log_div_log_log_of_ne_zero (hA : 0 ≤ A) (hC₀ : 0 < C₀)
    (hd : ∀ s : ℂ, 1 / 4 < s.re → 1 ≤ s.im → DifferentiableAt ℂ F s)
    (hG : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ s.im → ‖F s‖ ≤ C₀ * s.im ^ A)
    (hne : ∀ s : ℂ, 1 / 2 < s.re → 1 ≤ s.im → F s ≠ 0)
    (hK : ∀ s : ℂ, 3 / 2 ≤ s.re → 1 ≤ s.im →
      Real.exp (-K₂) ≤ ‖F s‖ ∧ ‖F s‖ ≤ Real.exp K₂) :
    ∃ C : ℝ, ∀ t : ℝ, 100 ≤ t →
      ‖F (1 / 2 + t * I)‖ ≤ Real.exp (C * Real.log t / Real.log (Real.log t)) := by
  obtain ⟨A₀, C₁, hC₁, hCA, hF⟩ :=
    exists_neg_mul_rpow_le_re_deriv_div_of_ne_zero hA hC₀ hd hG hne hK
  have hK₂ : 0 ≤ K₂ := by
    obtain ⟨h1, h2⟩ := hK (3 / 2 + I) (by simp) (by simp)
    have := Real.exp_le_exp.1 (h1.trans h2)
    linarith
  have hA₀ : 0 < A₀ := hC₁.trans_le hCA
  refine ⟨K₂ + 60 * A₀, fun t ht ↦ ?_⟩
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
  set M : ℝ := A₀ * L with hM
  have hM0 : 0 < M := mul_pos hA₀ hL0
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
  -- differentiability and nonvanishing on the horizontal line of height `t`
  have hpt : ∀ σ : ℝ, 1 / 4 < σ → DifferentiableAt ℂ F (σ + t * I) := fun σ hσ ↦
    hd _ (by simpa using hσ) (by simp; linarith)
  have hpt0 : ∀ σ : ℝ, 1 / 2 < σ → F (σ + t * I) ≠ 0 := fun σ hσ ↦
    hne _ (by simpa using hσ) (by simp; linarith)
  set Φ : ℝ → ℝ := fun σ ↦ Real.log ‖F (σ + t * I)‖ -
    60 * M / κ * Real.exp (-(κ * (σ - 1 / 2) / 15)) with hΦ
  have hΦd : ∀ σ : ℝ, 1 / 2 < σ → HasDerivAt Φ
      ((deriv F (σ + t * I) / F (σ + t * I)).re +
        4 * M * Real.exp (-(κ * (σ - 1 / 2) / 15))) σ := by
    intro σ hσ
    have hγ : HasDerivAt (fun y : ℝ ↦ F (y + t * I)) (deriv F (σ + t * I)) σ :=
      ((hpt σ (by linarith)).hasDerivAt.comp_add_const (σ : ℂ) (t * I)).comp_ofReal
    have h2 := Complex.hasDerivAt_log_norm hγ (hpt0 σ hσ)
    have h3 : HasDerivAt (fun y : ℝ ↦ 60 * M / κ * Real.exp (-(κ * (y - 1 / 2) / 15)))
        (60 * M / κ * (Real.exp (-(κ * (σ - 1 / 2) / 15)) * -(κ * 1 / 15))) σ :=
      ((((hasDerivAt_id σ).sub_const (1 / 2)).const_mul κ).div_const 15).neg.exp.const_mul _
    refine (h2.sub h3).congr_deriv ?_
    field_simp
    ring
  -- bound for every point to the right of the critical line
  have hbound : ∀ y : ℝ, 0 < y → y < 1 →
      ‖F ((1 / 2 + y : ℝ) + t * I)‖ ≤ Real.exp ((K₂ + 60 * A₀) * L / ℓ) := by
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
    have hK32 := hK (((3 / 2 : ℝ) : ℂ) + t * I) (by simp) (by simp; linarith)
    have h32pos : 0 < ‖F (((3 / 2 : ℝ) : ℂ) + t * I)‖ := (Real.exp_pos _).trans_le hK32.1
    have hlog32 : Real.log ‖F (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K₂ := by
      rw [Real.log_le_iff_le_exp h32pos]
      exact hK32.2
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
    have hMκ : 60 * M / κ ≤ 60 * A₀ * (L / ℓ) := by
      rw [hM, ← mul_assoc, mul_div_assoc (60 * A₀)]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hL0.le hℓ0 hκℓ) (by positivity)
    have hLℓ : 1 ≤ L / ℓ := (one_le_div hℓ0).2 hℓL
    have hfinal : Real.log ‖F ((1 / 2 + y : ℝ) + t * I)‖ ≤ (K₂ + 60 * A₀) * L / ℓ := by
      have : K₂ ≤ K₂ * (L / ℓ) := by nlinarith
      have e : (K₂ + 60 * A₀) * L / ℓ = K₂ * (L / ℓ) + 60 * A₀ * (L / ℓ) := by ring
      rw [e]
      linarith
    have hpos : 0 < ‖F ((1 / 2 + y : ℝ) + t * I)‖ :=
      norm_pos_iff.2 (hpt0 _ (by linarith))
    rwa [Real.log_le_iff_le_exp hpos] at hfinal
  -- let `y → 0`
  have e : (((1 / 2 + (0 : ℝ) : ℝ) : ℂ) + t * I) = 1 / 2 + (t : ℂ) * I := by
    push_cast; ring
  have hcont : ContinuousAt (fun y : ℝ ↦ ‖F ((1 / 2 + y : ℝ) + t * I)‖) 0 := by
    have h1 : ContinuousAt F (((1 / 2 + (0 : ℝ) : ℝ) : ℂ) + t * I) :=
      (hpt _ (by norm_num)).continuousAt
    have h2 : ContinuousAt (fun y : ℝ ↦ ((1 / 2 + y : ℝ) : ℂ) + t * I) 0 := by fun_prop
    exact (ContinuousAt.comp (f := fun y : ℝ ↦ ((1 / 2 + y : ℝ) : ℂ) + t * I) h1 h2).norm
  have hlim : Tendsto (fun y : ℝ ↦ ‖F ((1 / 2 + y : ℝ) + t * I)‖) (𝓝[>] 0)
      (𝓝 ‖F ((1 / 2 + (0 : ℝ) : ℝ) + t * I)‖) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ y : ℝ in 𝓝[>] 0, ‖F ((1 / 2 + y : ℝ) + t * I)‖ ≤
      Real.exp ((K₂ + 60 * A₀) * L / ℓ) := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with y hy
    exact hbound y hy.1 hy.2
  have hres := le_of_tendsto hlim hev
  rwa [e] at hres

end Lindelof
