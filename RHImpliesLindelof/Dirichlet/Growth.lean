import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Linear growth of Dirichlet `L`-functions in a vertical strip

For a nontrivial Dirichlet character `χ` modulo `N`, the partial sums of `χ` are bounded. By
Abel summation and analytic continuation this gives, for `0 < re s`, the representation
`L(s, χ) = s * ∫ t in Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * t ^ (-(s + 1))`, from which we deduce a
crude linear bound for `L(s, χ)` in the strip `1 / 4 ≤ re s ≤ 4` away from the real axis.

## Main results

* `DirichletCharacter.norm_sum_Icc_le`: `‖∑ k ∈ Icc 1 n, χ k‖ ≤ N + 1` for `χ ≠ 1`.
* `DirichletCharacter.LFunction_eq_mul_integral`: the integral representation of `L(s, χ)` on
  `0 < re s`.
* `DirichletCharacter.norm_LFunction_le_mul_abs_im`: `‖L(s, χ)‖ ≤ 20 * (N + 1) * |im s|` for
  `1 / 4 ≤ re s ≤ 4` and `1 ≤ |im s|`.
-/

open Complex Set MeasureTheory Filter Topology

namespace Lindelof

variable {u : ℝ → ℂ} {B : ℝ}

/-- For a bounded measurable function `u`, the integral `∫ t in Ioi 1, u t * t ^ (-(s + 1))` is
a Mellin transform of the truncation of `u` to `(1, ∞)`. -/
private lemma mellin_indicator_Ioi_neg (u : ℝ → ℂ) (s : ℂ) :
    mellin ((Ioi (1 : ℝ)).indicator u) (-s) = ∫ t in Ioi (1 : ℝ), u t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  have h : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (1 : ℝ)).indicator u t =
      (Ioi (1 : ℝ)).indicator (fun t : ℝ => u t * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
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

/-- For a bounded measurable function `u`, the integral `∫ t in Ioi 1, u t * t ^ (-(s + 1))` is
holomorphic in `s` on `0 < re s`. -/
lemma differentiableAt_integral_Ioi_mul_cpow (hu : Measurable u) (hB : ∀ t, ‖u t‖ ≤ B) {s : ℂ}
    (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ t in Ioi (1 : ℝ), u t * (t : ℂ) ^ (-(z + 1))) s := by
  set v : ℝ → ℂ := (Ioi (1 : ℝ)).indicator u with hv
  have hvB : ∀ t, ‖v t‖ ≤ B := by
    intro t
    by_cases h : t ∈ Ioi (1 : ℝ)
    · rw [hv, indicator_of_mem h]; exact hB t
    · rw [hv, indicator_of_notMem h, norm_zero]; exact (norm_nonneg _).trans (hB 0)
  have hJ : (fun z : ℂ => ∫ t in Ioi (1 : ℝ), u t * (t : ℂ) ^ (-(z + 1))) =
      fun z => mellin v (-z) := by
    ext z; exact (mellin_indicator_Ioi_neg u z).symm
  rw [hJ]
  have hm : DifferentiableAt ℂ (mellin v) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const B).mono
        (hu.indicator measurableSet_Ioi).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => (hvB t).trans (Real.le_norm_self B)
    · refine Asymptotics.IsBigO.of_bound B (Eventually.of_forall fun t => ?_)
      simpa using hvB t
    · simpa using hs
    · have : v =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℂ) := by
        have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
        filter_upwards [this] with t ht
        exact indicator_of_notMem (by simpa using (le_of_lt ht)) _
      exact this.trans_isBigO (Asymptotics.isBigO_zero _ _)
    · simp
  exact hm.comp s differentiableAt_id.neg

/-- For a function `u` bounded by `B`, the integral `∫ t in Ioi 1, u t * t ^ (-(s + 1))` is
bounded by `B / re s` on `0 < re s`. -/
lemma norm_integral_Ioi_mul_cpow_le (hB : ∀ t, ‖u t‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Ioi (1 : ℝ), u t * (t : ℂ) ^ (-(s + 1))‖ ≤ B / s.re := by
  have hint : IntegrableOn (fun t : ℝ => B * t ^ (-(s.re + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul B
  have hval : ∫ t in Ioi (1 : ℝ), B * t ^ (-(s.re + 1)) = B / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    rw [show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq, mul_one_div]
  rw [← hval]
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
  have hre : (-(s + 1)).re = -(s.re + 1) := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_right (hB t) (Real.rpow_nonneg ht0.le _)

end Lindelof

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The sum of a nontrivial Dirichlet character modulo `N` over `N` consecutive integers
vanishes. -/
lemma sum_range_add_eq_zero (hχ : χ ≠ 1) (n : ℕ) :
    ∑ j ∈ Finset.range N, χ ((n + j : ℕ) : ZMod N) = 0 := by
  have h1 : ∑ j ∈ Finset.range N, χ ((n + j : ℕ) : ZMod N) =
      ∑ a : ZMod N, χ ((n : ZMod N) + a) := by
    refine Finset.sum_nbij' (fun j => (j : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · intro j _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.2 (ZMod.val_lt a)
    · intro j hj
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (Finset.mem_range.1 hj)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro j _; push_cast; rfl
  rw [h1]
  exact (Equiv.sum_comp (Equiv.addLeft (n : ZMod N)) (fun a => χ a)).trans
    (MulChar.sum_eq_zero_of_ne_one hχ)

/-- The partial sums over `range n` of a nontrivial Dirichlet character modulo `N` are bounded
by `N`. -/
lemma norm_sum_range_le (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, χ (k : ZMod N)‖ ≤ N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n N with h | h
    · calc ‖∑ k ∈ Finset.range n, χ (k : ZMod N)‖
          ≤ ∑ k ∈ Finset.range n, ‖χ (k : ZMod N)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
        _ = n := by simp
        _ ≤ N := by exact_mod_cast h.le
    · have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
      rw [Finset.sum_range_add, sum_range_add_eq_zero hχ m, add_zero]
      exact ih m (by omega)

/-- The partial sums of a nontrivial Dirichlet character modulo `N` are bounded by `N + 1`. -/
lemma norm_sum_Icc_le (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod N)‖ ≤ N + 1 := by
  have h : ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod N) =
      ∑ k ∈ Finset.range (n + 1), χ (k : ZMod N) - χ ((0 : ℕ) : ZMod N) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), add_sub_cancel_left]
    rfl
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sum_range_le hχ _) (χ.norm_le_one _))

omit [NeZero N] in
private lemma measurable_sum_Icc_floor (χ : DirichletCharacter ℂ N) :
    Measurable (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) :=
  (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod N))).comp
    Nat.measurable_floor

/-- The integral representation of `L(s, χ)` for a nontrivial character `χ` and `0 < re s`,
obtained from Abel summation on `1 < re s` by analytic continuation. -/
theorem LFunction_eq_mul_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(s + 1)) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  set J : ℂ → ℂ := fun z => ∫ t in Ioi (1 : ℝ),
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N)) * (t : ℂ) ^ (-(z + 1)) with hJ
  let G : ℂ → ℂ := fun z => LFunction χ z - z * J z
  have hG : DifferentiableOn ℂ G U := by
    intro z hz
    have hJd : DifferentiableAt ℂ J z :=
      Lindelof.differentiableAt_integral_Ioi_mul_cpow (measurable_sum_Icc_floor χ)
        (fun t => norm_sum_Icc_le hχ _) hz
    exact ((differentiable_LFunction hχ z).sub
      (differentiableAt_id.mul hJd)).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G U := hG.analyticOnNhd hUo
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hzero : G =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod N)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
      refine Asymptotics.IsBigO.of_bound (N + 1) (Eventually.of_forall fun n => ?_)
      simpa using norm_sum_Icc_le hχ n
    have key := LSeries_eq_mul_integral (fun n : ℕ => χ (n : ZMod N)) le_rfl
      (zero_lt_one.trans hz) (LSeriesSummable_of_one_lt_re χ hz) hO
    simp only [G, Pi.zero_apply, LFunction_eq_LSeries χ hz, key, hJ, sub_self]
  have hGs : G s = 0 :=
    hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre (show (2 : ℂ) ∈ U by simp [hU])
      hzero hs
  exact sub_eq_zero.1 hGs

/-- A crude linear bound for the `L`-function of a nontrivial Dirichlet character modulo `N` in
the strip `1 / 4 ≤ re s ≤ 4`, away from the real axis: `‖L(s, χ)‖ ≤ 20 * (N + 1) * |im s|`
whenever `1 ≤ |im s|`. -/
theorem norm_LFunction_le_mul_abs_im (hχ : χ ≠ 1) {s : ℂ} (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 4)
    (h3 : 1 ≤ |s.im|) : ‖LFunction χ s‖ ≤ 20 * (N + 1) * |s.im| := by
  have hre : 0 < s.re := by linarith
  rw [LFunction_eq_mul_integral hχ hre, norm_mul]
  have hnorm : ‖s‖ ≤ 5 * |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 4 + |s.im| := by rw [abs_of_pos hre]; linarith
      _ ≤ 5 * |s.im| := by linarith
  have hN : (0 : ℝ) ≤ N + 1 := by positivity
  have hJ := Lindelof.norm_integral_Ioi_mul_cpow_le
    (u := fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N))
    (fun t => norm_sum_Icc_le hχ _) hre
  have hJ' : ((N : ℝ) + 1) / s.re ≤ 4 * (N + 1) := by
    rw [div_le_iff₀ hre]; nlinarith
  calc ‖s‖ * _ ≤ (5 * |s.im|) * (4 * (N + 1)) :=
        mul_le_mul hnorm (hJ.trans hJ') (norm_nonneg _) (by positivity)
    _ = 20 * (N + 1) * |s.im| := by ring

end DirichletCharacter
