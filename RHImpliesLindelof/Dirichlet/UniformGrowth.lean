import RHImpliesLindelof.Dirichlet.Growth

/-!
# Growth of Dirichlet `L`-functions, uniformly in the conductor and the height

For a nontrivial Dirichlet character `χ` modulo `N`, the integral representation
`DirichletCharacter.LFunction_eq_mul_integral` gives `‖L(s, χ)‖ ≤ ‖s‖ * ((N + 1) / re s)` on the
whole half-plane `0 < re s`. We record this bound and the consequences needed for the
conductor-uniform Lindelöf bound. All constants are absolute.

## Main results

* `DirichletCharacter.norm_LFunction_le_norm_mul_div_re`:
  `‖L(s, χ)‖ ≤ ‖s‖ * ((N + 1) / re s)` for `0 < re s`.
* `DirichletCharacter.norm_LFunction_le_four_mul_norm`: `‖L(s, χ)‖ ≤ 4 * (N + 1) * ‖s‖` for
  `1 / 4 ≤ re s`.
* `DirichletCharacter.norm_LFunction_le_of_dist_lt`: `‖L(s, χ)‖ ≤ 10 * (N * (|t| + 2))` for
  `1 / 2 ≤ re s` in the disc of centre `2 + t * I` and radius `3 / 2`.
* `DirichletCharacter.norm_LFunction_le_of_re_eq_quarter`:
  `‖L(s, χ)‖ ≤ 8 * (N * (|im s| + 2))` on the line `re s = 1 / 4`.
-/

open Complex

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- For a nontrivial character `χ` modulo `N`, `‖L(s, χ)‖ ≤ ‖s‖ * ((N + 1) / re s)` on the
half-plane `0 < re s`. -/
theorem norm_LFunction_le_norm_mul_div_re (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ ‖s‖ * ((N + 1) / s.re) := by
  rw [LFunction_eq_mul_integral hχ hs, norm_mul]
  exact mul_le_mul_of_nonneg_left (Lindelof.norm_integral_Ioi_mul_cpow_le
    (u := fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod N))
    (fun t => norm_sum_Icc_le hχ _) hs) (norm_nonneg _)

/-- For a nontrivial character `χ` modulo `N`, `‖L(s, χ)‖ ≤ 4 * (N + 1) * ‖s‖` on the
half-plane `1 / 4 ≤ re s`. -/
theorem norm_LFunction_le_four_mul_norm (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 4 ≤ s.re) :
    ‖LFunction χ s‖ ≤ 4 * (N + 1) * ‖s‖ := by
  have hre : 0 < s.re := by linarith
  have hN : (0 : ℝ) ≤ N + 1 := by positivity
  have h : ((N : ℝ) + 1) / s.re ≤ 4 * (N + 1) := by
    rw [div_le_iff₀ hre]; nlinarith
  calc ‖LFunction χ s‖ ≤ ‖s‖ * ((N + 1) / s.re) := norm_LFunction_le_norm_mul_div_re hχ hre
    _ ≤ ‖s‖ * (4 * (N + 1)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = 4 * (N + 1) * ‖s‖ := by ring

/-- For a nontrivial character `χ` modulo `N` and any real `t`,
`‖L(s, χ)‖ ≤ 10 * (N * (|t| + 2))` for all `s` with `1 / 2 ≤ re s` in the open disc of centre
`2 + t * I` and radius `3 / 2`. -/
theorem norm_LFunction_le_of_dist_lt (hχ : χ ≠ 1) {t : ℝ} {s : ℂ}
    (hs : dist s (2 + t * I) < 3 / 2) (hre : 1 / 2 ≤ s.re) :
    ‖LFunction χ s‖ ≤ 10 * (N * (|t| + 2)) := by
  have hre0 : 0 < s.re := by linarith
  have hs' : ‖s - (2 + t * I)‖ < 3 / 2 := by rwa [dist_eq_norm] at hs
  have h1 := (abs_re_le_norm (s - (2 + t * I))).trans_lt hs'
  have h2 := (abs_im_le_norm (s - (2 + t * I))).trans_lt hs'
  simp only [sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_im, add_im,
    mul_im, re_ofNat, im_ofNat, mul_zero, mul_one, sub_zero, zero_add, add_zero] at h1 h2
  rw [abs_lt] at h1
  have him : |s.im| ≤ |t| + 3 / 2 := by
    have := abs_sub_abs_le_abs_sub s.im t
    linarith
  have hnorm : ‖s‖ ≤ |t| + 5 := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ ≤ |t| + 5 := by rw [abs_of_pos hre0]; linarith [h1.2]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have ht : 0 ≤ |t| := abs_nonneg t
  have hdiv : ((N : ℝ) + 1) / s.re ≤ 4 * N := by
    rw [div_le_iff₀ hre0]; nlinarith
  calc ‖LFunction χ s‖ ≤ ‖s‖ * ((N + 1) / s.re) := norm_LFunction_le_norm_mul_div_re hχ hre0
    _ ≤ (|t| + 5) * (4 * N) := mul_le_mul hnorm hdiv (by positivity) (by positivity)
    _ ≤ 10 * (N * (|t| + 2)) := by nlinarith [mul_nonneg ht (zero_le_one.trans hN1)]

/-- For a nontrivial character `χ` modulo `N`, `‖L(s, χ)‖ ≤ 8 * (N * (|im s| + 2))` on the
line `re s = 1 / 4`. -/
theorem norm_LFunction_le_of_re_eq_quarter (hχ : χ ≠ 1) {s : ℂ} (hs : s.re = 1 / 4) :
    ‖LFunction χ s‖ ≤ 8 * (N * (|s.im| + 2)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have ht : 0 ≤ |s.im| := abs_nonneg _
  have hnorm : ‖s‖ ≤ 1 / 4 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ = 1 / 4 + |s.im| := by rw [hs]; norm_num
  calc ‖LFunction χ s‖ ≤ 4 * (N + 1) * ‖s‖ := norm_LFunction_le_four_mul_norm hχ hs.ge
    _ ≤ 4 * (N + 1) * (1 / 4 + |s.im|) := by gcongr
    _ ≤ 8 * (N * (|s.im| + 2)) := by nlinarith [mul_nonneg ht (zero_le_one.trans hN1)]

end DirichletCharacter
