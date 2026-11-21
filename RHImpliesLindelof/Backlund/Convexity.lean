import RHImpliesLindelof.HalfStrip
import RHImpliesLindelof.Moments
import RHImpliesLindelof.Sharp.LogDerivZeta

/-!
# The Lindelöf hypothesis to the right of the critical line

Two applications of the Phragmén–Lindelöf principle in a half-strip to the Riemann zeta
function, relating the Lindelöf hypothesis on the critical line to bounds to its right.

## Main results

* `Lindelof.exists_norm_riemannZeta_le_mul_im_rpow_of_isBigO`: if
  `ζ(1 / 2 + t * I) = O(t ^ η)`, then `‖ζ s‖ ≤ C * (im s) ^ η` uniformly on `1 / 2 ≤ re s`,
  `1 ≤ im s`.
* `Lindelof.isBigO_riemannZeta_of_forall_half_lt`: if `ζ(σ + t * I) = O(t ^ η)` for all
  `1 / 2 < σ ≤ 1` and all `η > 0`, then the Lindelöf hypothesis holds.
-/

open Complex

namespace Lindelof

/-- If `ζ(1 / 2 + t * I) = O(t ^ η)` as `t → ∞`, then `‖ζ s‖ ≤ C * (im s) ^ η` uniformly in the
quarter-plane `1 / 2 ≤ re s`, `1 ≤ im s`. -/
theorem exists_norm_riemannZeta_le_mul_im_rpow_of_isBigO {η : ℝ} (hη : 0 < η)
    (h : (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ η) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ s.im → ‖riemannZeta s‖ ≤ C * s.im ^ η := by
  obtain ⟨K₁, hK₁, h1⟩ := exists_norm_riemannZeta_le_mul_rpow_of_isBigO hη.le h
  obtain ⟨K₂, hK₂, h2⟩ := exists_exp_neg_le_norm_riemannZeta
  set M : ℝ := K₁ + Real.exp K₂ + 25 with hM
  have hMpos : 0 < M := by positivity
  have h3η : (1 : ℝ) ≤ 3 ^ η := Real.one_le_rpow (by norm_num) hη.le
  set g : ℂ → ℂ := fun s ↦ riemannZeta s * Complex.exp (-(η : ℂ) * Complex.log (-I * s))
    with hg
  have hnorm : ∀ s : ℂ, ‖g s‖ = ‖riemannZeta s‖ * Real.exp (-η * Real.log ‖s‖) := by
    intro s
    simp only [hg, norm_mul, Complex.norm_exp]
    congr 2
    have : (-(η : ℂ) * Complex.log (-I * s)).re = -η * (Complex.log (-I * s)).re := by
      rw [← ofReal_neg, re_ofReal_mul]
    rw [this, Complex.log_re]
    simp
  have hfac : ∀ s : ℂ, 1 ≤ s.im → Real.exp (-η * Real.log ‖s‖) ≤ s.im ^ (-η) ∧
      s.im ^ (-η) ≤ 1 := by
    intro s hs
    have h0 : 0 < s.im := by linarith
    have hle : s.im ≤ ‖s‖ := (le_abs_self _).trans (abs_im_le_norm s)
    refine ⟨?_, Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)⟩
    rw [Real.rpow_def_of_pos h0, Real.exp_le_exp]
    have := Real.log_le_log h0 hle
    nlinarith
  have hζ25 : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ s.im → ‖riemannZeta s‖ ≤ 25 * s.im := by
    intro s ha hb hs
    have h0 : 0 ≤ s.im := by linarith
    simpa only [abs_of_nonneg h0] using
      norm_riemannZeta_le_mul_abs_im (s := s) (by linarith) (by linarith)
        (by rwa [abs_of_nonneg h0])
  have hstrip : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ s.im → ‖g s‖ ≤ M := by
    intro s ha hb hs
    refine PhragmenLindelof.vertical_halfStrip_of_rpow_growth (g := g) (a := 1 / 2) (b := 2)
      (B := 25) (N := 1) (by norm_num) hMpos ?_ ?_ ?_ ha hb hs
    · intro z _ _ hz
      have hz1 : z ≠ 1 := by
        rintro rfl
        simp at hz
        linarith
      have hslit : -I * z ∈ slitPlane := by
        rw [mem_slitPlane_iff]
        left
        simp
        linarith
      exact (differentiableAt_riemannZeta hz1).mul
        (((differentiableAt_id.const_mul (-I)).clog hslit).const_mul _).cexp
    · intro z hza hzb hz hcase
      rw [hnorm]
      obtain ⟨hf1, hf2⟩ := hfac z hz
      have hz0 : 0 < z.im := by linarith
      rcases hcase with hc | hc | hc
      · have hzeq : z = 1 / 2 + (z.im : ℂ) * I := by
          apply Complex.ext <;> simp [hc]
        have hb1 := h1 z.im hz
        rw [← hzeq] at hb1
        calc ‖riemannZeta z‖ * Real.exp (-η * Real.log ‖z‖)
            ≤ K₁ * z.im ^ η * z.im ^ (-η) := by gcongr
          _ = K₁ := by
            rw [mul_assoc, ← Real.rpow_add hz0, add_neg_cancel, Real.rpow_zero, mul_one]
          _ ≤ M := by rw [hM]; linarith [Real.exp_pos K₂]
      · have hb2 := (h2 z (by linarith)).2
        calc ‖riemannZeta z‖ * Real.exp (-η * Real.log ‖z‖)
            ≤ Real.exp K₂ * 1 := by gcongr; exact hf1.trans hf2
          _ ≤ M := by rw [hM]; linarith
      · have hb3 := hζ25 z hza hzb hz
        rw [hc] at hb3
        calc ‖riemannZeta z‖ * Real.exp (-η * Real.log ‖z‖)
            ≤ 25 * 1 * 1 := by gcongr; exact hf1.trans hf2
          _ ≤ M := by rw [hM]; linarith [Real.exp_pos K₂]
    · intro z hza hzb hz
      rw [hnorm, Real.rpow_one]
      obtain ⟨hf1, hf2⟩ := hfac z hz
      calc ‖riemannZeta z‖ * Real.exp (-η * Real.log ‖z‖)
          ≤ 25 * z.im * 1 := by gcongr; exacts [hζ25 z hza hzb hz, hf1.trans hf2]
        _ = 25 * z.im := mul_one _
  refine ⟨M * 3 ^ η, by positivity, fun s ha hs ↦ ?_⟩
  have hs0 : 0 < s.im := by linarith
  have hpow : (1 : ℝ) ≤ s.im ^ η := Real.one_le_rpow hs hη.le
  rcases le_or_gt s.re 2 with hb | hb
  · have hb' := hstrip s ha hb hs
    rw [hnorm] at hb'
    have hspos : 0 < ‖s‖ := lt_of_lt_of_le hs0 ((le_abs_self _).trans (abs_im_le_norm s))
    have hsle : ‖s‖ ≤ 3 * s.im := by
      have := norm_le_abs_re_add_abs_im s
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re), abs_of_pos hs0] at this
      linarith
    have hexp : Real.exp (-η * Real.log ‖s‖) * ‖s‖ ^ η = 1 := by
      rw [Real.rpow_def_of_pos hspos, ← Real.exp_add]
      simp [mul_comm]
    calc ‖riemannZeta s‖
        = ‖riemannZeta s‖ * Real.exp (-η * Real.log ‖s‖) * ‖s‖ ^ η := by
          rw [mul_assoc, hexp, mul_one]
      _ ≤ M * (3 * s.im) ^ η := by gcongr
      _ = M * 3 ^ η * s.im ^ η := by
          rw [Real.mul_rpow (by norm_num) hs0.le, mul_assoc]
  · have hb2 := (h2 s (by linarith)).2
    calc ‖riemannZeta s‖ ≤ Real.exp K₂ := hb2
      _ ≤ M * 3 ^ η * s.im ^ η := by
        have hMK : Real.exp K₂ ≤ M := by rw [hM]; linarith
        have h31 : M ≤ M * 3 ^ η := le_mul_of_one_le_right hMpos.le h3η
        have : M * 3 ^ η ≤ M * 3 ^ η * s.im ^ η := le_mul_of_one_le_right (by positivity) hpow
        linarith

/-- If `ζ(σ + t * I) = O(t ^ η)` for every `1 / 2 < σ ≤ 1` and every `η > 0`, then the Lindelöf
hypothesis holds: `ζ(1 / 2 + t * I) = O(t ^ ε)` for every `ε > 0`. -/
theorem isBigO_riemannZeta_of_forall_half_lt
    (h : ∀ σ η : ℝ, 1 / 2 < σ → σ ≤ 1 → 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖riemannZeta (σ + t * I)‖ ≤ C * t ^ η) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε := by
  intro ε hε
  set η : ℝ := min (1 / 4) (ε / 16) with hη_def
  have hη_pos : 0 < η := lt_min (by norm_num) (by positivity)
  have hη_le : η ≤ 1 / 4 := min_le_left _ _
  have hη_le' : η ≤ ε / 16 := min_le_right _ _
  obtain ⟨C₁, hC₁, hS⟩ := h (1 / 2 + η) (ε / 2) (by linarith) (by linarith) (by linarith)
  set C : ℝ := max 25 C₁ with hC_def
  have hC0 : 25 ≤ C := le_max_left _ _
  have hC1 : C₁ ≤ C := le_max_right _ _
  have hd : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 + η → 1 ≤ s.im →
      DifferentiableAt ℂ riemannZeta s := fun s _ _ h3 ↦
    differentiableAt_riemannZeta (by rintro rfl; simp at h3; linarith)
  have hgrow : ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 1 / 2 + η → 1 ≤ s.im →
      ‖riemannZeta s‖ ≤ C * s.im ^ (1 : ℝ) := by
    intro s h1 h2 h3
    have h0 : 0 ≤ s.im := by linarith
    have := norm_riemannZeta_le_mul_abs_im (s := s) h1 (by linarith) (by rwa [abs_of_nonneg h0])
    rw [abs_of_nonneg h0] at this
    rw [Real.rpow_one]
    exact this.trans (mul_le_mul_of_nonneg_right hC0 h0)
  have hleft : ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C * t ^ (1 : ℝ) := by
    intro t ht
    have := hgrow (((1 / 4 : ℝ) : ℂ) + t * I) (by simp) (by simp; linarith) (by simpa using ht)
    simpa using this
  have hright : ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (((1 / 2 + η : ℝ) : ℂ) + t * I)‖ ≤ C * t ^ (ε / 2) := fun t ht ↦
    (hS t ht).trans (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg (by linarith) _))
  obtain ⟨C', hC', hfin⟩ :=
    PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_vertical_halfStrip (f := riemannZeta)
      (a := 1 / 4) (b := 1 / 2 + η) (α := 1) (β := ε / 2) (A := 1) (C := C) (by linarith)
      hd hgrow hleft hright (σ := 1 / 2) (by norm_num) (by linarith)
  have hexp : 1 + (ε / 2 - 1) * (1 / 2 - 1 / 4) / (1 / 2 + η - 1 / 4) ≤ ε := by
    have hd : (0 : ℝ) < 1 / 2 + η - 1 / 4 := by linarith
    have : 1 + (ε / 2 - 1) * (1 / 2 - 1 / 4) / (1 / 2 + η - 1 / 4)
        = (1 * (1 / 2 + η - 1 / 4) + (ε / 2 - 1) * (1 / 2 - 1 / 4)) / (1 / 2 + η - 1 / 4) := by
      rw [add_div, mul_div_assoc, mul_div_cancel_right₀ _ hd.ne']
    rw [this, div_le_iff₀ hd]
    nlinarith
  refine Asymptotics.IsBigO.of_bound C' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := by linarith
  have h' := hfin t ht
  have hcast : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by push_cast; rfl
  rw [hcast] at h'
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0 _)]
  exact h'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht hexp) hC'.le)

end Lindelof
