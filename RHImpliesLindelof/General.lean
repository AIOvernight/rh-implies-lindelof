import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import RHImpliesLindelof.BorelCaratheodory
import RHImpliesLindelof.HalfStrip
import RHImpliesLindelof.ThreeCircles

/-!
# The Lindelöf bound for a zero-free function with a bounded logarithm far to the right

This file contains the analytic core of Littlewood's proof that the Riemann Hypothesis implies
the Lindelöf Hypothesis, for an abstract function `F : ℂ → ℂ`. All hypotheses are only required
in the upper region `1 ≤ im s`, so that they hold both for Dirichlet `L`-functions and for `ζ`
(whose pole and trivial zeros lie on the real axis):

* `F` is holomorphic on `1 / 4 ≤ re s`, `1 ≤ im s`;
* `‖F s‖ ≤ C₀ * (im s) ^ A` on `1 / 4 ≤ re s ≤ 4`, `1 ≤ im s`;
* `F` does not vanish on `1 / 2 < re s`, `1 ≤ im s`;
* on `3 / 2 ≤ re s`, `1 ≤ im s`, `F s` has a logarithm of norm at most `K` (in practice, the
  logarithm of an absolutely convergent Euler product).

The proof has three steps: a holomorphic logarithm of `F` on discs centred at `2 + t * I`,
bounded by the Borel–Carathéodory theorem; Hadamard's three-circles theorem; and the
Phragmén–Lindelöf principle in a half-strip.

## Main results

* `Lindelof.exists_log_norm_le_of_ne_zero`: a holomorphic logarithm `g` of `F` on the disc of
  centre `2 + t * I` and radius `3 / 2 - δ`, with `‖g‖ ≤ C * log t` on the closed disc of radius
  `3 / 2 - 2 * δ` and `‖g‖ ≤ C` on the closed disc of radius `1 / 4`.
* `Lindelof.exists_norm_le_mul_rpow_of_half_lt`: `F (σ + t * I) = O(t ^ ε)` for fixed
  `1 / 2 < σ ≤ 1`.
* `Lindelof.isBigO_rpow_of_ne_zero`: `F (1 / 2 + t * I) = O(t ^ ε)` as `t → +∞`.
-/

open Complex Metric

namespace Lindelof

/-- In the region `1 ≤ im s`, let `F` be holomorphic and zero-free on `1 / 2 < re s`, of
polynomial growth in the strip `1 / 4 ≤ re s ≤ 4`, and with a logarithm bounded by `K` on
`3 / 2 ≤ re s`. Then for every
`0 < δ < 1 / 4` there is a constant `C` such that for all `t ≥ 3` the function `F` has a
holomorphic logarithm `g` on the open disc of centre `2 + t * I` and radius `3 / 2 - δ`,
satisfying `‖g‖ ≤ C * log t` on the closed disc of radius `3 / 2 - 2 * δ` and `‖g‖ ≤ C` on the
closed disc of radius `1 / 4`. -/
theorem exists_log_norm_le_of_ne_zero {F : ℂ → ℂ} {A C₀ K : ℝ} (hA : 0 ≤ A) (hC₀ : 0 < C₀)
    (hd : ∀ s : ℂ, 1 / 4 ≤ s.re → 1 ≤ s.im → DifferentiableAt ℂ F s)
    (hgrow : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ s.im → ‖F s‖ ≤ C₀ * s.im ^ A)
    (hne : ∀ s : ℂ, 1 / 2 < s.re → 1 ≤ s.im → F s ≠ 0)
    (hlog : ∀ s : ℂ, 3 / 2 ≤ s.re → 1 ≤ s.im → ∃ w : ℂ, exp w = F s ∧ ‖w‖ ≤ K) {δ : ℝ} (hδ : 0 < δ)
    (hδ4 : δ < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ t → ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball (2 + t * I) (3 / 2 - δ)) ∧
      (∀ s ∈ ball (2 + t * I) (3 / 2 - δ), exp (g s) = F s) ∧
      (∀ s ∈ closedBall (2 + t * I) (3 / 2 - 2 * δ), ‖g s‖ ≤ C * Real.log t) ∧
      (∀ s ∈ closedBall (2 + t * I) (1 / 4), ‖g s‖ ≤ C) := by
  have hK : 0 ≤ K := by
    obtain ⟨w, -, hw⟩ := hlog (2 + I) (by norm_num) (by simp)
    exact (norm_nonneg w).trans hw
  set L : ℝ := |Real.log C₀| with hLdef
  have hL : 0 ≤ L := abs_nonneg _
  refine ⟨6 * (L + 2 * A + 1 + K) / δ + (5 * K + 2), by positivity, fun t ht ↦ ?_⟩
  set c : ℂ := 2 + t * I with hc
  have hlog1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_three.le.trans ht
  -- geometry of the ball
  have hgeo : ∀ s ∈ ball c (3 / 2 - δ), |s.re - 2| < 3 / 2 - δ ∧ |s.im - t| < 3 / 2 - δ := by
    intro s hs
    have hs' : ‖s - c‖ < 3 / 2 - δ := by simpa [dist_eq_norm] using hs
    have h1 := abs_re_le_norm (s - c)
    have h2 := abs_im_le_norm (s - c)
    simp only [hc, sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_im, add_im,
      mul_im, re_ofNat, im_ofNat] at h1 h2
    simp only [mul_zero, mul_one, sub_zero, zero_add, add_zero] at h1 h2
    exact ⟨h1.trans_lt hs', h2.trans_lt hs'⟩
  have hre12 : ∀ s ∈ ball c (3 / 2 - δ), 1 / 2 < s.re := by
    intro s hs
    have hg := (hgeo s hs).1
    rw [abs_lt] at hg
    linarith [hg.1]
  have him1 : ∀ s ∈ ball c (3 / 2 - δ), 1 ≤ s.im := by
    intro s hs
    have hg := (hgeo s hs).2
    rw [abs_lt] at hg
    linarith [hg.1]
  have hne0 : ∀ s ∈ ball c (3 / 2 - δ), F s ≠ 0 := fun s hs ↦ hne s (hre12 s hs) (him1 s hs)
  have hFdiff : ∀ s ∈ ball c (3 / 2 - δ), DifferentiableAt ℂ F s := fun s hs ↦
    hd s (by linarith [hre12 s hs]) (him1 s hs)
  have hζd : DifferentiableOn ℂ F (ball c (3 / 2 - δ)) := fun s hs ↦
    (hFdiff s hs).differentiableWithinAt
  have hfd : DifferentiableOn ℂ (fun s ↦ deriv F s / F s) (ball c (3 / 2 - δ)) :=
    (hζd.deriv isOpen_ball).div hζd hne0
  have hcre : c.re = 2 := by simp [hc]
  have hcB : c ∈ ball c (3 / 2 - δ) := mem_ball_self (by linarith)
  obtain ⟨g₀, hg₀exp, hg₀K⟩ := hlog c (by rw [hcre]; norm_num) (him1 c hcB)
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
    have h0 := hne0 s hs
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
  have hre_le : ∀ s ∈ ball c (3 / 2 - δ), ∀ X : ℝ, ‖F s‖ ≤ X →
      (g s).re ≤ Real.log X := by
    intro s hs X hX
    rw [← hexp s hs, Complex.norm_exp] at hX
    rw [Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hX)]
    exact hX
  refine ⟨g, hgdiff, hexp, ?_, ?_⟩
  · -- outer bound
    intro s hs
    set M : ℝ := L + 2 * A * Real.log t + 1 with hM
    have hMpos : 0 < M := by positivity
    have hsub : ball c (3 / 2 - 3 * δ / 2) ⊆ ball c (3 / 2 - δ) :=
      ball_subset_ball (by linarith)
    have hre : ∀ z ∈ ball c (3 / 2 - 3 * δ / 2), (g z).re ≤ M := by
      intro z hz
      have hzB := hsub hz
      have hg := hgeo z hzB
      rw [abs_lt, abs_lt] at hg
      have himt : z.im ≤ t ^ 2 := by nlinarith [hg.2.2]
      have him0 : 0 ≤ z.im := zero_le_one.trans (him1 z hzB)
      have hb := hgrow z (by linarith [hg.1.1]) (by linarith [hg.1.2]) (him1 z hzB)
      have hb2 : ‖F z‖ ≤ C₀ * (t ^ 2) ^ A :=
        hb.trans (by gcongr)
      have h := hre_le z hzB _ hb2
      have ht0 : (0 : ℝ) < t := by linarith
      rw [Real.log_mul hC₀.ne' (by positivity), Real.log_rpow (by positivity),
        Real.log_pow] at h
      have := le_abs_self (Real.log C₀)
      rw [hM, hLdef]
      push_cast at h
      linarith
    have hbc := borelCaratheodory_closedBall (r := 3 / 2 - 2 * δ) hMpos (hgdiff.mono hsub) hre
      (by linarith) (by linarith) hs
    rw [hgc] at hbc
    have e1 : (3 / 2 - 3 * δ / 2) - (3 / 2 - 2 * δ) = δ / 2 := by ring
    rw [e1] at hbc
    refine hbc.trans ?_
    have hMle : M ≤ (L + 2 * A + 1) * Real.log t := by
      rw [hM]; nlinarith
    have hd2 : 0 < δ / 2 := by positivity
    have s1 : 2 * M * (3 / 2 - 2 * δ) / (δ / 2) ≤ 6 * ((L + 2 * A + 1) * Real.log t) / δ := by
      rw [div_le_div_iff₀ hd2 hδ]
      nlinarith [mul_nonneg hMpos.le hδ.le, mul_le_mul_of_nonneg_right hMle hδ.le]
    have s2 : ‖g₀‖ * (3 / 2 - 3 * δ / 2 + (3 / 2 - 2 * δ)) / (δ / 2) ≤
        6 * (K * Real.log t) / δ := by
      rw [div_le_div_iff₀ hd2 hδ]
      have : K ≤ K * Real.log t := by nlinarith
      have h' : ‖g₀‖ ≤ K * Real.log t := hg₀K.trans this
      nlinarith [mul_nonneg (norm_nonneg g₀) hδ.le, mul_le_mul_of_nonneg_right h' hδ.le,
        norm_nonneg g₀]
    have s3 : 0 ≤ (5 * K + 2) * Real.log t := by positivity
    calc _ ≤ 6 * ((L + 2 * A + 1) * Real.log t) / δ + 6 * (K * Real.log t) / δ :=
          add_le_add s1 s2
      _ ≤ (6 * (L + 2 * A + 1 + K) / δ + (5 * K + 2)) * Real.log t := by
        have : 6 * ((L + 2 * A + 1) * Real.log t) / δ + 6 * (K * Real.log t) / δ
            = 6 * (L + 2 * A + 1 + K) / δ * Real.log t := by ring
        rw [this]; linarith
  · -- inner bound
    intro s hs
    have hsub : ball c (1 / 2) ⊆ ball c (3 / 2 - δ) := ball_subset_ball (by linarith)
    have hre : ∀ z ∈ ball c (1 / 2), (g z).re ≤ K + 1 := by
      intro z hz
      have hzB := hsub hz
      have hz' : ‖z - c‖ < 1 / 2 := by simpa [dist_eq_norm] using hz
      have h1 := abs_re_le_norm (z - c)
      rw [sub_re, hcre, abs_le] at h1
      have hzre : 3 / 2 ≤ z.re := by linarith [h1.1]
      have hb : ‖F z‖ ≤ Real.exp K := by
        obtain ⟨w, hw, hwK⟩ := hlog z hzre (him1 z hzB)
        rw [← hw, Complex.norm_exp]
        exact Real.exp_le_exp.mpr ((re_le_norm _).trans hwK)
      have := hre_le z hzB _ hb
      rw [Real.log_exp] at this
      linarith
    have hbc := borelCaratheodory_closedBall (r := 1 / 4) (by positivity) (hgdiff.mono hsub) hre
      (by norm_num) (by norm_num) hs
    rw [hgc] at hbc
    refine hbc.trans ?_
    have : (0 : ℝ) ≤ 6 * (L + 2 * A + 1 + K) / δ := by positivity
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

/-- **Littlewood's bound** for a function `F` that, in the region `1 ≤ im s`, is holomorphic
and zero-free on `1 / 2 < re s`, of polynomial growth in the strip `1 / 4 ≤ re s ≤ 4`, and has
a bounded logarithm on `3 / 2 ≤ re s`: for every fixed `1 / 2 < σ ≤ 1` and every `ε > 0` there is a
constant `C > 0` such that `‖F (σ + t * I)‖ ≤ C * t ^ ε` for all `t ≥ 3`. -/
theorem exists_norm_le_mul_rpow_of_half_lt {F : ℂ → ℂ} {A C₀ K : ℝ} (hA : 0 ≤ A) (hC₀ : 0 < C₀)
    (hd : ∀ s : ℂ, 1 / 4 ≤ s.re → 1 ≤ s.im → DifferentiableAt ℂ F s)
    (hgrow : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ s.im → ‖F s‖ ≤ C₀ * s.im ^ A)
    (hne : ∀ s : ℂ, 1 / 2 < s.re → 1 ≤ s.im → F s ≠ 0)
    (hlog : ∀ s : ℂ, 3 / 2 ≤ s.re → 1 ≤ s.im → ∃ w : ℂ, exp w = F s ∧ ‖w‖ ≤ K) {σ ε : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ t → ‖F (σ + t * I)‖ ≤ C * t ^ ε := by
  set δ : ℝ := (σ - 1 / 2) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 / 4 := by rw [hδ]; linarith
  obtain ⟨C, hC, hg⟩ := exists_log_norm_le_of_ne_zero hA hC₀ hd hgrow hne hlog hδ0 hδ1
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

/-- **The Lindelöf bound** for a function `F` that, in the region `1 ≤ im s`, is holomorphic
on `1 / 4 ≤ re s`, zero-free on `1 / 2 < re s`, of polynomial growth in the strip
`1 / 4 ≤ re s ≤ 4`, and has a bounded logarithm on `3 / 2 ≤ re s`:
`F (1 / 2 + t * I) = O(t ^ ε)` as `t → +∞` for every `ε > 0`. -/
theorem isBigO_rpow_of_ne_zero {F : ℂ → ℂ} {A C₀ K : ℝ} (hA : 0 ≤ A) (hC₀ : 0 < C₀)
    (hd : ∀ s : ℂ, 1 / 4 ≤ s.re → 1 ≤ s.im → DifferentiableAt ℂ F s)
    (hG : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ s.im → ‖F s‖ ≤ C₀ * s.im ^ A)
    (hne : ∀ s : ℂ, 1 / 2 < s.re → 1 ≤ s.im → F s ≠ 0)
    (hlog : ∀ s : ℂ, 3 / 2 ≤ s.re → 1 ≤ s.im → ∃ w : ℂ, exp w = F s ∧ ‖w‖ ≤ K) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => F (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε := by
  intro ε hε
  set η : ℝ := min (1 / 4) (ε / (8 * A + 8)) with hη_def
  have h8 : (0 : ℝ) < 8 * A + 8 := by linarith
  have hη_pos : 0 < η := lt_min (by norm_num) (div_pos hε h8)
  have hη_le : η ≤ 1 / 4 := min_le_left _ _
  have hη_le' : η * (8 * A + 8) ≤ ε := by
    have : η ≤ ε / (8 * A + 8) := min_le_right _ _
    rwa [le_div_iff₀ h8] at this
  have hAη : A * η ≤ ε / 8 := by nlinarith
  obtain ⟨C₁, hC₁, hS⟩ := exists_norm_le_mul_rpow_of_half_lt hA hC₀ hd hG hne hlog
    (σ := 1 / 2 + η) (ε := ε / 2) (by linarith) (by linarith) (by linarith)
  have h3A : (1 : ℝ) ≤ 3 ^ A := Real.one_le_rpow (by norm_num) hA
  set C : ℝ := max C₀ (max C₁ (C₀ * 3 ^ A)) with hC_def
  have hC0 : C₀ ≤ C := le_max_left _ _
  have hC1 : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC2 : C₀ * 3 ^ A ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCpos : 0 < C := lt_of_lt_of_le hC₀ hC0
  -- interior growth
  have hgrow : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 + η → 1 ≤ s.im →
      ‖F s‖ ≤ C * s.im ^ A := by
    intro s h1 h2 h3
    have h0 : 0 ≤ s.im := by linarith
    have := hG s h1 (by linarith) h3
    exact this.trans (mul_le_mul_of_nonneg_right hC0 (Real.rpow_nonneg h0 _))
  have hdiff : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 + η → 1 ≤ s.im →
      DifferentiableAt ℂ F s := fun s h1 _ h3 ↦ hd s h1 h3
  have hleft : ∀ t : ℝ, 1 ≤ t → ‖F (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C * t ^ A := by
    intro t ht
    have := hgrow (((1 / 4 : ℝ) : ℂ) + t * I) (by simp) (by simp; linarith) (by simpa using ht)
    simpa using this
  have hright : ∀ t : ℝ, 1 ≤ t →
      ‖F (((1 / 2 + η : ℝ) : ℂ) + t * I)‖ ≤ C * t ^ (ε / 2) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    rcases le_or_gt 3 t with h3 | h3
    · have := hS t h3
      push_cast at this ⊢
      exact this.trans (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg ht0 _))
    · have h1 := hG (((1 / 2 + η : ℝ) : ℂ) + t * I) (by simp; linarith) (by simp; linarith)
        (by simpa using ht)
      have him : (((1 / 2 + η : ℝ) : ℂ) + t * I).im = t := by simp
      rw [him] at h1
      have h2 : t ^ A ≤ 3 ^ A := Real.rpow_le_rpow ht0 h3.le hA
      have h4 : (1 : ℝ) ≤ t ^ (ε / 2) := Real.one_le_rpow ht (by linarith)
      calc ‖F (((1 / 2 + η : ℝ) : ℂ) + t * I)‖ ≤ C₀ * t ^ A := h1
        _ ≤ C₀ * 3 ^ A := mul_le_mul_of_nonneg_left h2 hC₀.le
        _ ≤ C := hC2
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * t ^ (ε / 2) := mul_le_mul_of_nonneg_left h4 hCpos.le
  obtain ⟨C', hC', hfin⟩ :=
    PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_vertical_halfStrip (f := F)
      (a := 1 / 4) (b := 1 / 2 + η) (α := A) (β := ε / 2) (A := A) (C := C) (by linarith)
      hdiff hgrow hleft hright (σ := 1 / 2) (by norm_num) (by linarith)
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
