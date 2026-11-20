import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import RHImpliesLindelof.Growth
import RHImpliesLindelof.LogZeta
import RHImpliesLindelof.Sharp.LogDerivLowerBound

/-!
# The logarithmic derivative of `ζ` to the right of the critical line, under RH

Assuming the Riemann Hypothesis we bound `ζ' / ζ` in the half-plane `1 / 2 < re s`, with
constants that are uniform in the height.

## Main results

* `Lindelof.exists_norm_deriv_riemannZeta_div_le`: `‖ζ' / ζ‖ ≤ C` on `7 / 4 ≤ re s`
  (unconditional).
* `Lindelof.exists_neg_mul_log_le_re_deriv_riemannZeta_div`: under RH there is `A` with
  `-(A * log (im s)) ≤ re (ζ' s / ζ s)` for `1 / 2 < re s ≤ 5 / 2` and `3 ≤ im s`. This uses the
  one-sided Landau lemma `Complex.exists_neg_mul_log_le_re_deriv_div`: all zeros near `s` lie on
  the critical line, hence to the left of `s`.
* `Lindelof.exists_neg_mul_rpow_le_re_deriv_riemannZeta_div`: under RH there are `0 < C ≤ A`
  such that for `t ≥ 100` and `0 < x ≤ 1`, with `M = A * log t`,
  `-(4 * M * (C / M) ^ (x / 15)) ≤ re (ζ' / ζ) (1 / 2 + x + t * I)`. This is Hadamard's
  three-circles theorem applied to the bounded function `F / (F + 2 * M)`, `F = ζ' / ζ`.
-/

open Complex Metric

namespace Lindelof

/-- Two-sided bound for `‖ζ‖` on `3 / 2 ≤ re s`, from the Euler product. -/
lemma exists_exp_neg_le_norm_riemannZeta :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 3 / 2 ≤ s.re →
      Real.exp (-K) ≤ ‖riemannZeta s‖ ∧ ‖riemannZeta s‖ ≤ Real.exp K := by
  refine ⟨3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ), ?_, fun s hs ↦ ?_⟩
  · have : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
      tsum_nonneg fun p ↦ by positivity
    positivity
  · have h := norm_tsum_neg_log_one_sub_prime_cpow_le hs
    have h1 := abs_re_le_norm (∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)))
    rw [← riemannZeta_eulerProduct_exp_log (by linarith), Complex.norm_exp]
    rw [abs_le] at h1
    exact ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_exp.2 (by linarith)⟩

/-- The logarithmic derivative of `ζ` is bounded on `7 / 4 ≤ re s`. -/
theorem exists_norm_deriv_riemannZeta_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 7 / 4 ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ C := by
  obtain ⟨K, hK, hζ⟩ := exists_exp_neg_le_norm_riemannZeta
  refine ⟨Real.exp K / (1 / 4) / Real.exp (-K), by positivity, fun s hs ↦ ?_⟩
  have hre : ∀ w ∈ closedBall s (1 / 4), 3 / 2 ≤ w.re := by
    intro w hw
    have h1 := abs_re_le_norm (w - s)
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [sub_re, abs_le] at h1
    linarith
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | 1 < w.re} := fun w hw ↦
    (differentiableAt_riemannZeta (fun h ↦ by
      rw [h] at hw; simp at hw)).differentiableWithinAt
  have hsub : closedBall s (1 / 4) ⊆ {w : ℂ | 1 < w.re} := fun w hw ↦ by
    have := hre w hw
    change 1 < w.re
    linarith
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 4)
    (hd.diffContOnCl_ball hsub)
    (fun w hw ↦ (hζ w (hre w (sphere_subset_closedBall hw))).2)
  have hlow := (hζ s (by linarith)).1
  rw [norm_div]
  exact div_le_div₀ (by positivity) hcauchy (Real.exp_pos _) hlow

/-- Under the Riemann Hypothesis, `re (ζ' / ζ)` is bounded below by `-(A * log (im s))` in the
strip `1 / 2 < re s ≤ 5 / 2`, `3 ≤ im s`. -/
theorem exists_neg_mul_log_le_re_deriv_riemannZeta_div (hRH : RiemannHypothesis) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 5 / 2 → 3 ≤ s.im →
      -(A * Real.log s.im) ≤ (deriv riemannZeta s / riemannZeta s).re := by
  obtain ⟨K₂, hK₂, hζ⟩ := exists_exp_neg_le_norm_riemannZeta
  obtain ⟨K, hK, hL⟩ := exists_neg_mul_log_le_re_deriv_div (r₁ := 1) (r₂ := 9 / 8)
    (r := 5 / 4) (R := 11 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨K * (26 + K₂), by positivity, fun s hs1 hs2 hs3 ↦ ?_⟩
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
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c (11 / 8)) := by
    intro w hw
    refine (differentiableAt_riemannZeta fun h ↦ ?_).differentiableWithinAt
    have := (hgeo (mem_ball.1 hw).le).2
    rw [h, abs_le] at this
    simp at this
    linarith
  have hB : ∀ w ∈ closedBall c (5 / 4), ‖riemannZeta w‖ ≤ 25 * (τ + 2) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hgeo (mem_closedBall.1 hw)
    rw [abs_le] at h1 h2
    have him : 0 < w.im := by linarith
    have := norm_riemannZeta_le_mul_abs_im (s := w) (by linarith) (by linarith)
      (by rw [abs_of_pos him]; linarith)
    rw [abs_of_pos him] at this
    linarith
  have hcζ := (hζ c (by rw [hcre])).1
  have hc0 : riemannZeta c ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le hcζ)
  have hzero : ∀ ρ ∈ closedBall c (9 / 8), riemannZeta ρ = 0 → ρ.re ≤ 1 / 2 := by
    intro ρ hρ h0
    obtain ⟨-, h2⟩ := hgeo (mem_closedBall.1 hρ)
    rw [abs_le] at h2
    have him : 0 < ρ.im := by linarith
    refine (hRH ρ h0 ?_ ?_).le
    · rintro ⟨n, hn⟩
      have := congrArg Complex.im hn
      simp at this
      linarith
    · intro h
      rw [h] at him
      simp at him
  have hsc : s ∈ closedBall c 1 := by
    rw [mem_closedBall, dist_eq_norm]
    have : s - c = ((s.re - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc, hτ]
    rw [this, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have key := hL riemannZeta c (1 / 2) (25 * (τ + 2)) hdiff hB hc0 hzero s hsc hs1
  refine le_trans ?_ key
  have hτpos : 0 < τ := by linarith
  have hlogτ : 1 ≤ Real.log τ := by
    rw [Real.le_log_iff_exp_le hτpos]
    exact Real.exp_one_lt_three.le.trans hs3
  have hcpos : 0 < ‖riemannZeta c‖ := norm_pos_iff.2 hc0
  have h1 : Real.log (25 * (τ + 2) / ‖riemannZeta c‖) ≤ (26 + K₂) * Real.log τ := by
    have hB0 : 0 < 25 * (τ + 2) := by positivity
    calc Real.log (25 * (τ + 2) / ‖riemannZeta c‖)
        ≤ Real.log (25 * τ ^ 2 * Real.exp K₂) := by
          refine Real.log_le_log (div_pos hB0 hcpos) ?_
          rw [div_le_iff₀ hcpos]
          have h3 : (1 : ℝ) ≤ Real.exp K₂ * ‖riemannZeta c‖ := by
            calc (1 : ℝ) = Real.exp K₂ * Real.exp (-K₂) := by
                  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
              _ ≤ Real.exp K₂ * ‖riemannZeta c‖ :=
                  mul_le_mul_of_nonneg_left hcζ (Real.exp_pos _).le
          have h4 : 25 * (τ + 2) ≤ 25 * τ ^ 2 := by nlinarith
          calc 25 * (τ + 2) ≤ 25 * τ ^ 2 * 1 := by linarith
            _ ≤ 25 * τ ^ 2 * (Real.exp K₂ * ‖riemannZeta c‖) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = 25 * τ ^ 2 * Real.exp K₂ * ‖riemannZeta c‖ := by ring
      _ = Real.log 25 + 2 * Real.log τ + K₂ := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
            Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp]
          push_cast; ring
      _ ≤ (26 + K₂) * Real.log τ := by
          have h25 : Real.log 25 ≤ 24 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 25)
            linarith
          nlinarith
  have := mul_le_mul_of_nonneg_left h1 hK
  rw [mul_assoc]
  linarith

/-- If `-M ≤ re z` with `M > 0`, then `‖z‖ ≤ ‖z + 2 * M‖`. -/
private lemma norm_le_norm_add_two_mul {z : ℂ} {M : ℝ} (hM : 0 < M) (hz : -M ≤ z.re) :
    ‖z‖ ≤ ‖z + 2 * (M : ℂ)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, re_ofNat, im_ofNat, ofReal_re, ofReal_im]
  nlinarith

/-- Under the Riemann Hypothesis, `re (ζ' / ζ) (1 / 2 + x + t * I)` is bounded below by
`-(4 * M * (C / M) ^ (x / 15))` with `M = A * log t`, uniformly for `0 < x ≤ 1` and
`t ≥ 100`. -/
theorem exists_neg_mul_rpow_le_re_deriv_riemannZeta_div (hRH : RiemannHypothesis) :
    ∃ A C : ℝ, 0 < C ∧ C ≤ A ∧ ∀ t : ℝ, 100 ≤ t → ∀ x : ℝ, 0 < x → x ≤ 1 →
      -(4 * (A * Real.log t) * (C / (A * Real.log t)) ^ (x / 15)) ≤
        (deriv riemannZeta (1 / 2 + x + t * I) / riemannZeta (1 / 2 + x + t * I)).re := by
  obtain ⟨A₁, hA₁, hlow⟩ := exists_neg_mul_log_le_re_deriv_riemannZeta_div hRH
  obtain ⟨C, hC, hbdd⟩ := exists_norm_deriv_riemannZeta_div_le
  refine ⟨2 * A₁ + C, C, hC, by linarith, fun t ht x hx0 hx1 ↦ ?_⟩
  have ht0 : 0 < t := by linarith
  have hlog : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]
    exact Real.exp_one_lt_three.le.trans (by linarith)
  set M : ℝ := (2 * A₁ + C) * Real.log t with hM
  have hMC : C ≤ M := by rw [hM]; nlinarith
  have hMA : 2 * A₁ * Real.log t ≤ M := by rw [hM]; nlinarith
  have hMpos : 0 < M := hC.trans_le hMC
  set F : ℂ → ℂ := fun s ↦ deriv riemannZeta s / riemannZeta s with hF
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
  have hne1 : ∀ w ∈ ball c (3 / 2), w ≠ 1 := by
    intro w hw h
    have := (hgeo (mem_ball.1 hw).le).2
    rw [h, abs_le] at this
    simp at this
    linarith
  have hre : ∀ w ∈ ball c (3 / 2), 1 / 2 < w.re ∧ w.re < 7 / 2 := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - c)
    simp only [hc, sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, re_ofNat] at h1
    simp only [mul_zero, mul_one, sub_zero, add_zero] at h1
    have := h1.trans_lt hw
    rw [abs_lt] at this
    constructor <;> linarith
  have hne0 : ∀ w ∈ ball c (3 / 2), riemannZeta w ≠ 0 := by
    intro w hw h0
    have h2 := (hgeo (mem_ball.1 hw).le).2
    rw [abs_le] at h2
    have := hRH w h0 (by
      rintro ⟨n, hn⟩
      have := congrArg Complex.im hn
      simp at this
      linarith) (hne1 w hw)
    linarith [(hre w hw).1]
  have hζd : DifferentiableOn ℂ riemannZeta (ball c (3 / 2)) := fun w hw ↦
    (differentiableAt_riemannZeta (hne1 w hw)).differentiableWithinAt
  have hFd : DifferentiableOn ℂ F (ball c (3 / 2)) := (hζd.deriv isOpen_ball).div hζd hne0
  -- lower bound for `re F` on the whole disc
  have hFre : ∀ w ∈ ball c (3 / 2), -M ≤ (F w).re := by
    intro w hw
    rcases le_total w.re (5 / 2) with h | h
    · have h2 := (hgeo (mem_ball.1 hw).le).2
      rw [abs_le] at h2
      have him : 3 ≤ w.im := by linarith
      have h3 := hlow w (hre w hw).1 h him
      have h4 : Real.log w.im ≤ 2 * Real.log t := by
        rw [← Real.log_rpow ht0]
        refine Real.log_le_log (by linarith) ?_
        rw [Real.rpow_two]
        nlinarith
      have h5 : A₁ * Real.log w.im ≤ M := by
        have := mul_le_mul_of_nonneg_left h4 hA₁
        linarith
      linarith
    · have h3 := hbdd w (by linarith)
      have h4 := abs_re_le_norm (F w)
      rw [abs_le] at h4
      have : ‖F w‖ ≤ M := h3.trans hMC
      linarith
  have hden : ∀ w ∈ ball c (3 / 2), F w + 2 * (M : ℂ) ≠ 0 := by
    intro w hw h0
    have := congrArg Complex.re h0
    simp only [add_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, zero_re] at this
    linarith [hFre w hw]
  set H : ℂ → ℂ := fun w ↦ F w / (F w + 2 * (M : ℂ)) with hH
  have hHd : DifferentiableOn ℂ H (ball c (3 / 2)) :=
    hFd.div (hFd.add_const _) hden
  have hH1 : ∀ w ∈ ball c (3 / 2), ‖H w‖ ≤ 1 := by
    intro w hw
    rw [hH, norm_div]
    exact div_le_one_of_le₀ (norm_le_norm_add_two_mul hMpos (hFre w hw)) (norm_nonneg _)
  set q : ℝ := C / M with hq
  have hq0 : 0 < q := div_pos hC hMpos
  have hq1 : q ≤ 1 := (div_le_one hMpos).2 hMC
  have hHq : ∀ w ∈ sphere c (1 / 4), ‖H w‖ ≤ q := by
    intro w hw
    have hwB : w ∈ ball c (3 / 2) := by
      rw [mem_sphere] at hw; rw [mem_ball, hw]; norm_num
    have h1 := (hgeo (mem_sphere.1 hw).le).1
    rw [abs_le] at h1
    have h3 : ‖F w‖ ≤ C := hbdd w (by linarith)
    have h4 : M ≤ ‖F w + 2 * (M : ℂ)‖ := by
      have h5 := Complex.re_le_norm (F w + 2 * (M : ℂ))
      simp only [add_re, mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im] at h5
      have h6 := abs_re_le_norm (F w)
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
  -- back from `H` to `F`
  have hqx : 0 < q ^ (x / 15) := Real.rpow_pos_of_pos hq0 _
  change -(4 * M * q ^ (x / 15)) ≤ (F z).re
  rcases le_or_gt (q ^ (x / 15)) (1 / 2) with hsmall | hbig
  · have hHhalf : ‖H z‖ ≤ 1 / 2 := hHz.trans hsmall
    have hrel : F z * (1 - H z) = 2 * (M : ℂ) * H z := by
      have hd := hden z hzB
      simp only [hH]
      field_simp
      ring
    have h1 := congrArg norm hrel
    rw [norm_mul, norm_mul, norm_mul, norm_ofNat, norm_real, Real.norm_of_nonneg hMpos.le] at h1
    have h2 : 1 - ‖H z‖ ≤ ‖1 - H z‖ := by
      have := norm_sub_norm_le (1 : ℂ) (H z)
      rwa [norm_one] at this
    have h3 : ‖F z‖ * (1 / 2) ≤ 2 * M * ‖H z‖ := by
      rw [← h1]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h4 : 2 * M * ‖H z‖ ≤ 2 * M * q ^ (x / 15) :=
      mul_le_mul_of_nonneg_left hHz (by positivity)
    have h5 := abs_re_le_norm (F z)
    rw [abs_le] at h5
    linarith
  · have := hFre z hzB
    nlinarith

end Lindelof
