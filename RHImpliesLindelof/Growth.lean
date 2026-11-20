import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Polynomial growth of the Riemann zeta function in a vertical strip

For `0 < re s` and `s ≠ 1` we prove the classical representation
`ζ(s) = s / (s - 1) - s * ∫ t in Ioi 1, {t} * t ^ (-(s + 1))`, where `{t}` is the fractional
part of `t`, and deduce a crude polynomial bound for `ζ` in the strip `1 / 4 ≤ re s ≤ 4` away
from the real axis.

## Main results

* `Lindelof.riemannZeta_eq_div_sub_mul_fractIntegral`: the integral representation of `ζ` on
  `0 < re s`, `s ≠ 1`.
* `Lindelof.norm_riemannZeta_le_mul_abs_im`: `‖ζ(s)‖ ≤ 25 * |im s|` for `1 / 4 ≤ re s ≤ 4` and
  `1 ≤ |im s|`.
* `Lindelof.exists_norm_riemannZeta_le_mul_abs_im_rpow`: the same bound in the existential form
  `‖ζ(s)‖ ≤ C * |im s| ^ A` used by the other files.
-/

open Complex Set MeasureTheory Filter Topology

noncomputable section

namespace Lindelof

/-- Fractional part, cut off to `(1, ∞)`, complex valued. -/
def fractIndicator : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ))

/-- The integral `∫ t in Ioi 1, {t} * t ^ (-(s + 1))`, where `{t}` is the fractional part. -/
def fractIntegral (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

lemma measurable_ofReal_fract : Measurable (fun t : ℝ => ((Int.fract t : ℝ) : ℂ)) :=
  Complex.measurable_ofReal.comp measurable_fract

lemma norm_ofReal_fract_le_one (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

lemma norm_fractIndicator_le_one (t : ℝ) : ‖fractIndicator t‖ ≤ 1 := by
  unfold fractIndicator
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem h]; exact norm_ofReal_fract_le_one t
  · rw [indicator_of_notMem h]; simp

lemma measurable_fractIndicator : Measurable fractIndicator :=
  measurable_ofReal_fract.indicator measurableSet_Ioi

lemma mellin_fractIndicator_neg (s : ℂ) : mellin fractIndicator (-s) = fractIntegral s := by
  unfold mellin fractIntegral
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • fractIndicator t =
      (Ioi (1 : ℝ)).indicator
        (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    unfold fractIndicator
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, mul_comm]
      congr 2; ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi]
  congr 2
  ext t
  simp only [mem_inter_iff, mem_Ioi]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨zero_lt_one.trans h, h⟩

lemma differentiableAt_fractIntegral {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ fractIntegral s := by
  have hJ : fractIntegral = fun s => mellin fractIndicator (-s) := by
    ext s; exact (mellin_fractIndicator_neg s).symm
  rw [hJ]
  have hm : DifferentiableAt ℂ (mellin fractIndicator) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const (1 : ℝ)).mono
        measurable_fractIndicator.aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => by simpa using norm_fractIndicator_le_one t
    · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
      simpa using norm_fractIndicator_le_one t
    · simpa using hs
    · have : fractIndicator =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℂ) := by
        have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
        filter_upwards [this] with t ht
        unfold fractIndicator
        exact indicator_of_notMem (by simpa using (le_of_lt ht)) _
      exact this.trans_isBigO (Asymptotics.isBigO_zero _ _)
    · simp
  exact hm.comp s differentiableAt_id.neg

lemma integrableOn_Ioi_cpow_neg_add_one {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
  integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one

lemma integrableOn_Ioi_fract_mul_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
  (integrableOn_Ioi_cpow_neg_add_one hs).bdd_mul (c := 1)
    measurable_ofReal_fract.aestronglyMeasurable
    (Eventually.of_forall norm_ofReal_fract_le_one)

/-- The integral representation of `ζ` for `1 < re s`, from Abel summation. -/
lemma riemannZeta_eq_mul_sub_fractIntegral_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * (1 / (s - 1) - fractIntegral s) := by
  have h0 : 0 < s.re := zero_lt_one.trans hs
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℕ → ℂ) k‖) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp
  have key := LSeries_eq_mul_integral' (1 : ℕ → ℂ) (r := 1) zero_le_one hs hO
  rw [LSeries_one_eq_riemannZeta hs] at key
  rw [key]
  congr 1
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one
  have hcongr : ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Ioi (1 : ℝ), ((t : ℂ) ^ (-s) -
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    have hfl : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      have h1 : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
        rw [← Int.self_sub_floor, sub_sub_cancel]
        exact natCast_floor_eq_intCast_floor ht0.le
      rw [← ofReal_sub, ← h1, ofReal_natCast]
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = -(s + 1) + 1 by ring, cpow_add _ _ htC, cpow_one, mul_comm]
    simp only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
      nsmul_eq_mul, mul_one]
    rw [hfl, hpow]; ring
  rw [hcongr, integral_sub hint1 (integrableOn_Ioi_fract_mul_cpow h0),
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one]
  simp only [fractIntegral, ofReal_one, one_cpow]
  congr 1
  have : s - 1 ≠ 0 := fun h => by
    have := congrArg re h
    simp at this; linarith
  have h2 : -s + 1 ≠ 0 := fun h => this (by linear_combination -h)
  field_simp
  ring

/-- The integral representation `ζ(s) = s / (s - 1) - s * ∫ t in Ioi 1, {t} * t ^ (-(s + 1))`
for `0 < re s`, `s ≠ 1`, by analytic continuation from `1 < re s`. -/
lemma riemannZeta_eq_div_sub_mul_fractIntegral {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * fractIntegral s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  let G : ℂ → ℂ := fun z => riemannZeta₁ z - z + z * (z - 1) * fractIntegral z
  have hG : DifferentiableOn ℂ G U := by
    intro z hz
    have hJ := differentiableAt_fractIntegral (s := z) hz
    have h1 : DifferentiableAt ℂ riemannZeta₁ z := differentiable_riemannZeta₁ z
    exact (((h1.sub differentiableAt_id).add
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hJ))).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G U := hG.analyticOnNhd hUo
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hzero : G =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
    have hz1 : z ≠ 1 := fun h => by simp [h] at hz
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    have e1 := riemannZeta_eq_mul_sub_fractIntegral_of_one_lt_re hz
    rw [riemannZeta_eq_inv_sub_mul hz1] at e1
    have e2 : riemannZeta₁ z = (z - 1) * (z * (1 / (z - 1) - fractIntegral z)) := by
      rw [← e1]; field_simp
    simp only [G, Pi.zero_apply, e2]
    field_simp
    ring
  have hall := hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre
    (show (2 : ℂ) ∈ U by simp [hU]) hzero
  have hGs : G s = 0 := hall hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  rw [riemannZeta_eq_inv_sub_mul hs1]
  have : riemannZeta₁ s = s - s * (s - 1) * fractIntegral s := by
    simp only [G] at hGs
    linear_combination hGs
  rw [this]
  field_simp

lemma norm_fractIntegral_le {s : ℂ} (hs : 0 < s.re) : ‖fractIntegral s‖ ≤ 1 / s.re := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hval : ∫ t in Ioi (1 : ℝ), t ^ (-(s.re + 1)) = 1 / s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    rw [show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]
  rw [← hval]
  unfold fractIntegral
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
  have hre : (-(s + 1)).re = -(s.re + 1) := by simp
  rw [hre]
  calc ‖((Int.fract t : ℝ) : ℂ)‖ * t ^ (-(s.re + 1))
      ≤ 1 * t ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right (norm_ofReal_fract_le_one t) (Real.rpow_nonneg ht0.le _)
    _ = t ^ (-(s.re + 1)) := one_mul _

/-- A crude linear bound for `ζ` in the strip `1 / 4 ≤ re s ≤ 4`, away from the real axis:
`‖ζ(s)‖ ≤ 25 * |im s|` whenever `1 ≤ |im s|`. -/
theorem norm_riemannZeta_le_mul_abs_im {s : ℂ} (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 4)
    (h3 : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 25 * |s.im| := by
  have hre : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := fun h => by
    rw [h] at h3; simp at h3; linarith
  rw [riemannZeta_eq_div_sub_mul_fractIntegral hre hs1]
  have ht0 : 0 ≤ |s.im| := abs_nonneg _
  have hnorm : ‖s‖ ≤ 5 * |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 4 + |s.im| := by rw [abs_of_pos hre]; linarith
      _ ≤ 5 * |s.im| := by linarith
  have hsub : 1 ≤ ‖s - 1‖ := by
    have : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  have hJ : ‖fractIntegral s‖ ≤ 4 := by
    refine (norm_fractIntegral_le hre).trans ?_
    rw [div_le_iff₀ hre]; linarith
  have hA : ‖s / (s - 1)‖ ≤ 5 * |s.im| := by
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) hsub).trans hnorm
  have hB : ‖s * fractIntegral s‖ ≤ 20 * |s.im| := by
    rw [norm_mul]
    calc ‖s‖ * ‖fractIntegral s‖ ≤ (5 * |s.im|) * 4 :=
          mul_le_mul hnorm hJ (norm_nonneg _) (by positivity)
      _ = 20 * |s.im| := by ring
  calc ‖s / (s - 1) - s * fractIntegral s‖ ≤ ‖s / (s - 1)‖ + ‖s * fractIntegral s‖ :=
        norm_sub_le _ _
    _ ≤ 5 * |s.im| + 20 * |s.im| := add_le_add hA hB
    _ = 25 * |s.im| := by ring

/-- Polynomial growth of `ζ` in the strip `1 / 4 ≤ re s ≤ 4`, away from the real axis: there are
`A ≥ 0` and `C > 0` with `‖ζ(s)‖ ≤ C * |im s| ^ A` whenever `1 ≤ |im s|`. -/
theorem exists_norm_riemannZeta_le_mul_abs_im_rpow :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A :=
  ⟨1, 25, zero_le_one, by norm_num, fun s h1 h2 h3 => by
    simpa only [Real.rpow_one] using norm_riemannZeta_le_mul_abs_im h1 h2 h3⟩

end Lindelof
