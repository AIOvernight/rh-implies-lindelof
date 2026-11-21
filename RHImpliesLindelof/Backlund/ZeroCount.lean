import Mathlib.NumberTheory.LSeries.Nonvanishing
import RHImpliesLindelof.Backlund.Convexity
import RHImpliesLindelof.Backlund.ZeroFactorization

/-!
# Counting the zeros of the Riemann zeta function in a box of height one

For real `σ` and `T`, `Lindelof.zetaZeroCount σ T` is the number of zeros `ρ` of `ζ`, counted
with multiplicity, in the box `σ < re ρ`, `T < im ρ ≤ T + 1`. For `σ > 1 / 2` and `T` large this
box, intersected with `re ρ < 1`, lies in a disc centred far to the right on which `ζ` is
holomorphic with `1 / 2 ≤ re s`, and the Jensen-type bound of
`Lindelof.exists_isZeroFactorization` bounds the count by the logarithm of the supremum of
`‖ζ‖` on the quarter-plane `1 / 2 ≤ re s`, `1 ≤ im s ≤ T + A`.

## Main definitions and results

* `Lindelof.zetaZeroBox`, `Lindelof.zetaZeroCount`: the box of zeros and the count.
* `Lindelof.exists_zetaZeroCount_mul_le`: the Jensen-type bound.
* `Lindelof.exists_finite_zetaZeroBox`: the box is finite for large `T`.
* `Lindelof.zetaZeroCount_isLittleO_log_of_lindelof`: under the Lindelöf hypothesis,
  `zetaZeroCount σ T = o(log T)` for every `σ > 1 / 2`.
-/

open Complex Metric

namespace Lindelof

/-- The set of zeros `ρ` of `ζ` with `σ < re ρ` and `T < im ρ ≤ T + 1`. -/
def zetaZeroBox (σ T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ T < ρ.im ∧ ρ.im ≤ T + 1}

/-- The number of zeros `ρ` of `ζ` with `σ < re ρ` and `T < im ρ ≤ T + 1`, counted with
multiplicity. -/
noncomputable def zetaZeroCount (σ T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ zetaZeroBox σ T, (analyticOrderAt riemannZeta ρ).toNat

/-- **Jensen-type bound for the zeros of `ζ` in a box.** For `σ > 1 / 2` there are `lam > 0`,
`A`, `T₀` and `K` such that for `T ≥ T₀`: if `‖ζ s‖ ≤ B` for `1 / 2 ≤ re s`,
`1 ≤ im s ≤ T + A`, then the box `σ < re ρ`, `T < im ρ ≤ T + 1` contains finitely many zeros
and their number, counted with multiplicity, is at most `(log B + K) / lam`. -/
theorem exists_zetaZeroCount_mul_le {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ lam A T₀ K : ℝ, 0 < lam ∧ 0 < A ∧ ∀ T : ℝ, T₀ ≤ T → ∀ B : ℝ,
      (∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ s.im → s.im ≤ T + A → ‖riemannZeta s‖ ≤ B) →
      (zetaZeroBox σ T).Finite ∧ zetaZeroCount σ T * lam ≤ Real.log B + K := by
  obtain ⟨K, hK, hζ⟩ := exists_exp_neg_le_norm_riemannZeta
  set u : ℝ := σ - 1 / 2 with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  set A : ℝ := 2 + σ + 1 / u with hA
  have hinv : 0 < 1 / u := by positivity
  have hA2 : 5 / 2 < A := by rw [hA]; linarith
  set r₂ : ℝ := √((A - σ) ^ 2 + 1 / 4) with hr₂
  set r : ℝ := A - 1 / 2 with hr
  have hr₂pos : 0 < r₂ := Real.sqrt_pos.2 (by positivity)
  have hrpos : 0 < r := by rw [hr]; linarith
  have h2r : r₂ < r := by
    rw [hr₂, Real.sqrt_lt' hrpos, hr]
    have h1 : u * (1 / u) = 1 := mul_one_div_cancel hu0.ne'
    have h2 : (A - 1 / 2) ^ 2 - (A - σ) ^ 2 = u * (7 / 2 + σ) + 2 * (u * (1 / u)) := by
      rw [hA, hu]; ring
    have h3 : 0 < u * (7 / 2 + σ) := by positivity
    linarith
  refine ⟨Real.log (r / r₂), A, A, K, Real.log_pos ((one_lt_div hr₂pos).2 h2r), by linarith,
    fun T hT B hB ↦ ?_⟩
  set c : ℂ := A + ((T + 1 / 2 : ℝ) : ℂ) * I with hc
  have hcre : c.re = A := by simp [hc]
  have hcim : c.im = T + 1 / 2 := by simp [hc]
  have hgeo : ∀ {ρ : ℝ} {w : ℂ}, dist w c ≤ ρ → |w.re - A| ≤ ρ ∧ |w.im - (T + 1 / 2)| ≤ ρ := by
    intro ρ w hw
    rw [dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - c)
    have h2 := abs_im_le_norm (w - c)
    rw [sub_re, hcre] at h1
    rw [sub_im, hcim] at h2
    exact ⟨h1.trans hw, h2.trans hw⟩
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c (A - 1 / 4)) := by
    intro w hw
    have hg := (hgeo (mem_ball.1 hw).le).2
    rw [abs_le] at hg
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    rintro rfl
    simp at hg
    linarith [hg.1]
  have hBc : ∀ w ∈ closedBall c r, ‖riemannZeta w‖ ≤ B := by
    intro w hw
    obtain ⟨h1, h2⟩ := hgeo (mem_closedBall.1 hw)
    rw [abs_le] at h1 h2
    exact hB w (by linarith [h1.1]) (by linarith [h2.1]) (by linarith [h2.2])
  have hc1 := (hζ c (by rw [hcre]; linarith)).1
  have hcpos : 0 < ‖riemannZeta c‖ := (Real.exp_pos _).trans_le hc1
  have hcne : riemannZeta c ≠ 0 := norm_pos_iff.1 hcpos
  obtain ⟨Z, g, hfact, hcard⟩ := exists_isZeroFactorization hr₂pos h2r
    (by rw [hr]; linarith : r < A - 1 / 4) hdiff hBc hcne
  have hS : zetaZeroBox σ T ⊆ closedBall c r₂ := by
    rintro ρ ⟨hρ0, hρσ, hρT, hρT'⟩
    have hρ1 : ρ.re < 1 := by
      by_contra hcon
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hcon) hρ0
    rw [mem_closedBall, dist_eq_norm, Complex.norm_def, normSq_apply, hr₂]
    refine Real.sqrt_le_sqrt ?_
    rw [sub_re, sub_im, hcre, hcim]
    nlinarith
  have hS0 : ∀ ρ ∈ zetaZeroBox σ T, riemannZeta ρ = 0 := fun ρ hρ ↦ hρ.1
  refine ⟨hfact.finite_of_subset h2r hS hS0, ?_⟩
  have hcount : zetaZeroCount σ T ≤ Z.card := hfact.finsum_toNat_analyticOrderAt_le_card h2r hS hS0
  have hlam : 0 < Real.log (r / r₂) := Real.log_pos ((one_lt_div hr₂pos).2 h2r)
  have hBpos : 0 < B := hcpos.trans_le (hBc c (mem_closedBall_self hrpos.le))
  have hlogc : -K ≤ Real.log ‖riemannZeta c‖ := by
    rw [Real.le_log_iff_exp_le hcpos]
    exact hc1
  calc (zetaZeroCount σ T : ℝ) * Real.log (r / r₂)
      ≤ Z.card * Real.log (r / r₂) := by gcongr
    _ ≤ Real.log (B / ‖riemannZeta c‖) := hcard
    _ = Real.log B - Real.log ‖riemannZeta c‖ := Real.log_div hBpos.ne' hcpos.ne'
    _ ≤ Real.log B + K := by linarith

/-- For `σ > 1 / 2` and `T` large, the box `σ < re ρ`, `T < im ρ ≤ T + 1` contains finitely
many zeros of `ζ`. -/
theorem exists_finite_zetaZeroBox {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → (zetaZeroBox σ T).Finite := by
  obtain ⟨lam, A, T₀, K, -, hA, hmain⟩ := exists_zetaZeroCount_mul_le hσ
  obtain ⟨K₂, -, hζ⟩ := exists_exp_neg_le_norm_riemannZeta
  refine ⟨T₀, fun T hT ↦ (hmain T hT (25 * (T + A) + Real.exp K₂) fun s h1 h2 h3 ↦ ?_).1⟩
  have h0 : 0 ≤ s.im := by linarith
  rcases le_or_gt s.re 4 with h4 | h4
  · have := norm_riemannZeta_le_mul_abs_im (s := s) (by linarith) h4
      (by rwa [abs_of_nonneg h0])
    rw [abs_of_nonneg h0] at this
    linarith [Real.exp_pos K₂]
  · have := (hζ s (by linarith)).2
    nlinarith

/-- **The Lindelöf hypothesis implies that `ζ` has few zeros to the right of the critical
line**: the number of zeros with `σ < re ρ`, `T < im ρ ≤ T + 1` is `o(log T)` for every
`σ > 1 / 2`. -/
theorem zetaZeroCount_isLittleO_log_of_lindelof
    (h : ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    (fun T : ℝ => (zetaZeroCount σ T : ℝ)) =o[Filter.atTop] Real.log := by
  obtain ⟨lam, A, T₀, K, hlam, hA, hmain⟩ := exists_zetaZeroCount_mul_le hσ
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  set η : ℝ := ε * lam / 2 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨C, hC, hbound⟩ := exists_norm_riemannZeta_le_mul_im_rpow_of_isBigO hη0 (h η hη0)
  filter_upwards [Filter.eventually_ge_atTop T₀, Filter.eventually_ge_atTop A,
    Filter.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop
      ((Real.log C + K + η * Real.log 2) / η)] with T hT₀ hTA hT1 hTlog
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hB : ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ s.im → s.im ≤ T + A →
      ‖riemannZeta s‖ ≤ C * (2 * T) ^ η := by
    intro s h1 h2 h3
    refine (hbound s h1 h2).trans ?_
    gcongr
    linarith
  have hm := (hmain T hT₀ _ hB).2
  rw [Real.log_mul hC.ne' (by positivity), Real.log_rpow (by positivity),
    Real.log_mul (by norm_num) hT0.ne'] at hm
  rw [div_le_iff₀ hη0] at hTlog
  rw [Real.norm_natCast, Real.norm_of_nonneg hlogT]
  have hfin : (zetaZeroCount σ T : ℝ) * lam ≤ ε * Real.log T * lam := by
    have : ε * Real.log T * lam = 2 * η * Real.log T := by rw [hη]; ring
    rw [this]
    nlinarith
  exact le_of_mul_le_mul_right hfin hlam

end Lindelof
