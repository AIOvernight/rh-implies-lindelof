import Mathlib.Analysis.Complex.Liouville
import RHImpliesLindelof.Growth

/-!
# The Lindelöf hypothesis and moments of the Riemann zeta function

We prove the classical equivalence (Titchmarsh, *The theory of the Riemann zeta-function*,
Theorem 13.2) between the Lindelöf hypothesis and the bounds
`∫ t in 1..T, ‖ζ(1 / 2 + t * I)‖ ^ (2 * k) = O(T ^ (1 + ε))` for all even moments of `ζ` on the
critical line. This is an unconditional equivalence between two open statements.

## Main results

* `integral_norm_riemannZeta_pow_isBigO_of_lindelof`: Lindelöf implies the moment bounds.
* `lindelof_of_integral_norm_riemannZeta_pow_isBigO`: the moment bounds imply Lindelöf.
* `lindelof_iff_integral_norm_riemannZeta_pow_isBigO`: the equivalence.

## Auxiliary results

* `Lindelof.norm_deriv_riemannZeta_le`: `‖ζ'(1 / 2 + t * I)‖ ≤ 100 * (t + 1 / 4)` for `2 ≤ t`,
  by the Cauchy estimate and the crude bound `Lindelof.norm_riemannZeta_le_mul_abs_im`.
* `Lindelof.norm_riemannZeta_pow_le_mul_integral`: for `2 ≤ t`,
  `‖ζ(1 / 2 + t * I)‖ ^ (2 * k + 1) ≤ 2 ^ (2 * k + 1) * (100 * (t + 2)) * ∫ u in 1..(t + 1),
  ‖ζ(1 / 2 + u * I)‖ ^ (2 * k)`: a large value of `ζ` persists on a short interval, hence
  contributes to the moment.
-/

open Complex Set Filter Asymptotics MeasureTheory

namespace Lindelof

/-- Points of the critical line are different from the pole of `ζ`. -/
lemma one_half_add_mul_I_ne_one (t : ℝ) : (1 / 2 + t * I : ℂ) ≠ 1 := by
  intro h
  have h' := congrArg Complex.re h
  norm_num at h'

/-- The derivative of `t ↦ ζ(1 / 2 + t * I)`. -/
lemma hasDerivAt_riemannZeta_one_half_add_mul_I (u : ℝ) :
    HasDerivAt (fun t : ℝ => riemannZeta (1 / 2 + t * I))
      (deriv riemannZeta (1 / 2 + u * I) * I) u := by
  have h1 : HasDerivAt riemannZeta (deriv riemannZeta (1 / 2 + u * I)) (1 / 2 + (u : ℂ) * I) :=
    (differentiableAt_riemannZeta (one_half_add_mul_I_ne_one u)).hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => 1 / 2 + z * I) I (u : ℂ) := by
    simpa using ((hasDerivAt_id (u : ℂ)).mul_const I).const_add (1 / 2)
  exact (HasDerivAt.comp (u : ℂ) h1 h2).comp_ofReal

/-- The function `t ↦ ζ(1 / 2 + t * I)` is continuous. -/
lemma continuous_riemannZeta_one_half_add_mul_I :
    Continuous fun t : ℝ => riemannZeta (1 / 2 + t * I) :=
  continuous_iff_continuousAt.2 fun u =>
    (hasDerivAt_riemannZeta_one_half_add_mul_I u).continuousAt

/-- A linear bound for `ζ'` on the critical line, from the Cauchy estimate on a circle of
radius `1 / 4`. -/
lemma norm_deriv_riemannZeta_le {t : ℝ} (ht : 2 ≤ t) :
    ‖deriv riemannZeta (1 / 2 + t * I)‖ ≤ 100 * (t + 1 / 4) := by
  have key : ∀ z : ℂ, ‖z - (1 / 2 + t * I)‖ ≤ 1 / 4 →
      1 / 4 ≤ z.re ∧ z.re ≤ 3 / 4 ∧ t - 1 / 4 ≤ z.im ∧ z.im ≤ t + 1 / 4 := by
    intro z hz
    have hre := (Complex.abs_re_le_norm (z - (1 / 2 + t * I))).trans hz
    have him := (Complex.abs_im_le_norm (z - (1 / 2 + t * I))).trans hz
    have e1 : (z - (1 / 2 + t * I)).re = z.re - 1 / 2 := by simp
    have e2 : (z - (1 / 2 + t * I)).im = z.im - t := by simp
    rw [e1, abs_le] at hre
    rw [e2, abs_le] at him
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hd : DiffContOnCl ℂ riemannZeta (Metric.ball (1 / 2 + t * I) (1 / 4)) := by
    refine differentiableOn_riemannZeta.diffContOnCl_ball fun z hz => ?_
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    obtain ⟨-, -, h3, -⟩ := key z hz
    rintro rfl
    simp only [one_im] at h3
    linarith
  have hC : ∀ z ∈ Metric.sphere (1 / 2 + t * I : ℂ) (1 / 4),
      ‖riemannZeta z‖ ≤ 25 * (t + 1 / 4) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    obtain ⟨h1, h2, h3, h4⟩ := key z hz.le
    have h0 : 0 ≤ z.im := by linarith
    have := norm_riemannZeta_le_mul_abs_im h1 (by linarith)
      (by rw [abs_of_nonneg h0]; linarith)
    rw [abs_of_nonneg h0] at this
    linarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hd hC
  linarith

/-- On `[t, t + 1]`, the function `u ↦ ζ(1 / 2 + u * I)` is Lipschitz with constant
`100 * (t + 2)`. -/
lemma norm_riemannZeta_sub_le {t u : ℝ} (ht : 2 ≤ t) (hu : u ∈ Icc t (t + 1)) :
    ‖riemannZeta (1 / 2 + u * I) - riemannZeta (1 / 2 + t * I)‖ ≤ 100 * (t + 2) * (u - t) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun x : ℝ => riemannZeta (1 / 2 + x * I))
    (f' := fun x : ℝ => deriv riemannZeta (1 / 2 + x * I) * I)
    (fun x _ => (hasDerivAt_riemannZeta_one_half_add_mul_I x).hasDerivWithinAt)
    (fun x hx => ?_) u hu
  rw [norm_mul, norm_I, mul_one]
  have := norm_deriv_riemannZeta_le (ht.trans hx.1)
  linarith [hx.2]

/-- A value of `ζ` on the critical line is controlled by a moment: the value persists (up to a
factor `2`) on an interval of length proportional to it. -/
lemma norm_riemannZeta_pow_le_mul_integral {t : ℝ} (ht : 2 ≤ t) (k : ℕ) :
    ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k + 1) ≤
      2 ^ (2 * k + 1) * (100 * (t + 2)) *
        ∫ u in (1 : ℝ)..(t + 1), ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k) := by
  have ht0 : 0 ≤ t := by linarith
  have hM25 : ‖riemannZeta (1 / 2 + t * I)‖ ≤ 25 * t := by
    have := norm_riemannZeta_le_mul_abs_im (s := 1 / 2 + t * I) (by norm_num) (by norm_num)
      (by simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re]
          norm_num
          rw [abs_of_nonneg ht0]; linarith)
    simpa [abs_of_nonneg ht0] using this
  set M := ‖riemannZeta (1 / 2 + t * I)‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hL : 0 < 100 * (t + 2) := by linarith
  set h := M / (2 * (100 * (t + 2))) with hh
  have hh0 : 0 ≤ h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one (by positivity)]
    linarith
  have hcont : Continuous fun u : ℝ => ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k) :=
    continuous_riemannZeta_one_half_add_mul_I.norm.pow _
  have hlow : ∀ u ∈ Icc t (t + h),
      (M / 2) ^ (2 * k) ≤ ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k) := by
    intro u hu
    have h1 := norm_riemannZeta_sub_le ht (u := u) ⟨hu.1, by linarith [hu.2]⟩
    have h2 : M - ‖riemannZeta (1 / 2 + u * I)‖ ≤
        ‖riemannZeta (1 / 2 + u * I) - riemannZeta (1 / 2 + t * I)‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le _ _
    have h3 : 100 * (t + 2) * (u - t) ≤ 100 * (t + 2) * h :=
      mul_le_mul_of_nonneg_left (by linarith [hu.2]) hL.le
    have h4 : 100 * (t + 2) * h = M / 2 := by
      rw [hh]
      field_simp
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hint : h * (M / 2) ^ (2 * k) ≤
      ∫ u in (1 : ℝ)..(t + 1), ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k) :=
    calc h * (M / 2) ^ (2 * k) = ∫ _ in t..(t + h), (M / 2) ^ (2 * k) := by simp
      _ ≤ ∫ u in t..(t + h), ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k) :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          (hcont.intervalIntegrable _ _) hlow
      _ ≤ ∫ u in (1 : ℝ)..(t + 1), ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k) :=
        intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
          (Eventually.of_forall fun u => by positivity) (hcont.intervalIntegrable _ _)
  have hid : M ^ (2 * k + 1) =
      2 ^ (2 * k + 1) * (100 * (t + 2)) * (h * (M / 2) ^ (2 * k)) := by
    rw [hh, div_pow, pow_succ 2 (2 * k), pow_succ M (2 * k)]
    field_simp
  rw [hid]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

/-- A bound `ζ(1 / 2 + t * I) = O(t ^ ε)` at infinity can be made uniform on `[1, ∞)`. -/
lemma exists_norm_riemannZeta_le_mul_rpow_of_isBigO {ε : ℝ} (hε : 0 ≤ ε)
    (h : (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[atTop] fun t : ℝ => t ^ ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 1 ≤ t → ‖riemannZeta (1 / 2 + t * I)‖ ≤ K * t ^ ε := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨a, ha⟩ := eventually_atTop.1 hC
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := max a 1)).exists_bound_of_continuousOn
    continuous_riemannZeta_one_half_add_mul_I.continuousOn
  refine ⟨|B| + |C|, by positivity, fun t ht => ?_⟩
  have ht1 : 1 ≤ t ^ ε := Real.one_le_rpow ht hε
  rcases le_total t (max a 1) with h1 | h1
  · calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ B := hB t ⟨ht, h1⟩
      _ ≤ (|B| + |C|) * 1 := by linarith [le_abs_self B, abs_nonneg C]
      _ ≤ (|B| + |C|) * t ^ ε := mul_le_mul_of_nonneg_left ht1 (by positivity)
  · have h2 := ha t ((le_max_left _ _).trans h1)
    rw [Real.norm_of_nonneg (by positivity)] at h2
    calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * t ^ ε := h2
      _ ≤ (|B| + |C|) * t ^ ε :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C, abs_nonneg B]) (by positivity)

end Lindelof

open Lindelof

/-- Lindelöf implies that every even moment of ζ on the critical line is `O(T^(1+ε))`. -/
theorem integral_norm_riemannZeta_pow_isBigO_of_lindelof
    (h : ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε) :
    ∀ (k : ℕ) (ε : ℝ), 0 < ε →
      (fun T : ℝ => ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
        =O[Filter.atTop] fun T : ℝ => T ^ (1 + ε) := by
  intro k ε hε
  have hn : (0 : ℝ) < 2 * k + 1 := by positivity
  have hδ : 0 < ε / (2 * k + 1) := div_pos hε hn
  obtain ⟨K, hK0, hK⟩ := exists_norm_riemannZeta_le_mul_rpow_of_isBigO hδ.le (h _ hδ)
  refine IsBigO.of_bound (K ^ (2 * k)) (eventually_atTop.2 ⟨1, fun T hT => ?_⟩)
  have hT0 : 0 < T := by linarith
  have hexp : ε / (2 * k + 1) * ((2 * k : ℕ) : ℝ) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    push_cast
    nlinarith
  have hpt : ∀ x ∈ Set.uIoc (1 : ℝ) T,
      ‖‖riemannZeta (1 / 2 + x * I)‖ ^ (2 * k)‖ ≤ K ^ (2 * k) * T ^ ε := by
    intro x hx
    rw [uIoc_of_le hT] at hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖riemannZeta (1 / 2 + x * I)‖ ^ (2 * k)
        ≤ (K * T ^ (ε / (2 * k + 1))) ^ (2 * k) := by
          refine pow_le_pow_left₀ (norm_nonneg _) ((hK x hx.1.le).trans ?_) _
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx.2 hδ.le) hK0
      _ = K ^ (2 * k) * T ^ (ε / (2 * k + 1) * ((2 * k : ℕ) : ℝ)) := by
          rw [mul_pow, Real.rpow_mul_natCast hT0.le]
      _ ≤ K ^ (2 * k) * T ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp) (by positivity)
  calc ‖∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k)‖
      ≤ K ^ (2 * k) * T ^ ε * |T - 1| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ ≤ K ^ (2 * k) * T ^ ε * T := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [abs_of_nonneg (by linarith)]
        linarith
    _ = K ^ (2 * k) * ‖T ^ (1 + ε)‖ := by
        rw [Real.norm_of_nonneg (by positivity), Real.rpow_add hT0, Real.rpow_one]
        ring

/-- Conversely, if every even moment is `O(T^(1+ε))`, then Lindelöf holds. -/
theorem lindelof_of_integral_norm_riemannZeta_pow_isBigO
    (h : ∀ (k : ℕ) (ε : ℝ), 0 < ε →
      (fun T : ℝ => ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
        =O[Filter.atTop] fun T : ℝ => T ^ (1 + ε)) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε := by
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 3 / ε ≤ k := exists_nat_ge _
  obtain ⟨E, hE⟩ := (h k 1 one_pos).bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hE
  have hn0 : 2 * k + 1 ≠ 0 := by omega
  have hnpos : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hexp : 3 * (((2 * k + 1 : ℕ) : ℝ))⁻¹ ≤ ε := by
    rw [← div_eq_mul_inv, div_le_iff₀ hnpos]
    rw [div_le_iff₀ hε] at hk
    push_cast
    nlinarith
  refine IsBigO.of_bound ((2 ^ (2 * k + 1) * 800 * |E|) ^ (((2 * k + 1 : ℕ) : ℝ))⁻¹)
    (eventually_atTop.2 ⟨max 2 T₀, fun t ht => ?_⟩)
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := by linarith
  have hint : (∫ u in (1 : ℝ)..(t + 1), ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k)) ≤
      |E| * (2 * t) ^ 2 := by
    have h1 := hT₀ (t + 1) (by linarith [(le_max_right 2 T₀).trans ht])
    have h2 : (t + 1) ^ ((1 : ℝ) + 1) = (t + 1) ^ 2 := by
      rw [one_add_one_eq_two, Real.rpow_two]
    rw [h2, Real.norm_of_nonneg (sq_nonneg (t + 1))] at h1
    calc (∫ u in (1 : ℝ)..(t + 1), ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k))
        ≤ E * (t + 1) ^ 2 := (Real.le_norm_self _).trans h1
      _ ≤ |E| * (t + 1) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)
      _ ≤ |E| * (2 * t) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _)
          (abs_nonneg E)
  have hpow : ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k + 1) ≤
      2 ^ (2 * k + 1) * 800 * |E| * t ^ 3 :=
    calc ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k + 1)
        ≤ 2 ^ (2 * k + 1) * (100 * (t + 2)) *
          ∫ u in (1 : ℝ)..(t + 1), ‖riemannZeta (1 / 2 + u * I)‖ ^ (2 * k) :=
          norm_riemannZeta_pow_le_mul_integral ht2 k
      _ ≤ 2 ^ (2 * k + 1) * (100 * (t + 2)) * (|E| * (2 * t) ^ 2) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ ≤ 2 ^ (2 * k + 1) * (100 * (2 * t)) * (|E| * (2 * t) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 ^ (2 * k + 1) * 800 * |E| * t ^ 3 := by ring
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖riemannZeta (1 / 2 + t * I)‖
      = (‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k + 1)) ^ (((2 * k + 1 : ℕ) : ℝ))⁻¹ :=
        (Real.pow_rpow_inv_natCast (norm_nonneg _) hn0).symm
    _ ≤ (2 ^ (2 * k + 1) * 800 * |E| * t ^ 3) ^ (((2 * k + 1 : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (2 ^ (2 * k + 1) * 800 * |E|) ^ (((2 * k + 1 : ℕ) : ℝ))⁻¹ *
          t ^ (3 * (((2 * k + 1 : ℕ) : ℝ))⁻¹) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast t 3,
          ← Real.rpow_mul ht0]
        norm_num
    _ ≤ (2 ^ (2 * k + 1) * 800 * |E|) ^ (((2 * k + 1 : ℕ) : ℝ))⁻¹ * t ^ ε :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) (by positivity)

/-- The Lindelöf hypothesis is equivalent to the bound `O(T^(1+ε))` for every even moment of
ζ on the critical line. -/
theorem lindelof_iff_integral_norm_riemannZeta_pow_isBigO :
    (∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε) ↔
    ∀ (k : ℕ) (ε : ℝ), 0 < ε →
      (fun T : ℝ => ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
        =O[Filter.atTop] fun T : ℝ => T ^ (1 + ε) :=
  ⟨integral_norm_riemannZeta_pow_isBigO_of_lindelof,
    lindelof_of_integral_norm_riemannZeta_pow_isBigO⟩
