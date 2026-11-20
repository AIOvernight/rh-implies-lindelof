import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import RHImpliesLindelof.General
import RHImpliesLindelof.Growth
import RHImpliesLindelof.LogZeta

/-!
# The Riemann Hypothesis implies the Lindelöf Hypothesis

We prove Littlewood's theorem that the Riemann Hypothesis implies the Lindelöf Hypothesis
`ζ(1 / 2 + t * I) = O(|t| ^ ε)` for every `ε > 0`.

The proof applies the abstract statement `Lindelof.isBigO_rpow_of_ne_zero` to `ζ`, using the
linear growth bound `Lindelof.norm_riemannZeta_le_mul_abs_im`, the non-vanishing of `ζ` on
`1 / 2 < re s`, `0 < im s` under RH, and the Euler product. The case `t → -∞` follows from the
symmetry `ζ(conj s) = conj (ζ s)`.

## Main results

* `Lindelof.exists_norm_riemannZeta_le_mul_rpow_of_half_lt`: under RH, for `1 / 2 < σ ≤ 1` and
  `ε > 0` there is `C > 0` with `‖ζ(σ + t * I)‖ ≤ C * t ^ ε` for all `t ≥ 3`.
* `lindelof_of_riemannHypothesis`: under RH, `ζ(1 / 2 + t * I) = O(t ^ ε)` as `t → +∞`.
* `lindelof_atBot_of_riemannHypothesis`: under RH, `ζ(1 / 2 + t * I) = O(|t| ^ ε)` as `t → -∞`.
-/

open Complex

namespace Lindelof

private lemma differentiableAt_riemannZeta_of_one_le_im (s : ℂ) (_ : 1 / 4 ≤ s.re)
    (him : 1 ≤ s.im) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta (by rintro rfl; simp at him; linarith)

private lemma norm_riemannZeta_le_mul_im_rpow (s : ℂ) (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 4)
    (h3 : 1 ≤ s.im) : ‖riemannZeta s‖ ≤ 25 * s.im ^ (1 : ℝ) := by
  have h0 : 0 ≤ s.im := zero_le_one.trans h3
  simpa only [Real.rpow_one, abs_of_nonneg h0] using
    norm_riemannZeta_le_mul_abs_im h1 h2 (by rwa [abs_of_nonneg h0])

private lemma exists_exp_eq_riemannZeta (s : ℂ) (hs : 3 / 2 ≤ s.re) (_ : 1 ≤ s.im) :
    ∃ w : ℂ, exp w = riemannZeta s ∧
      ‖w‖ ≤ 3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
  ⟨_, riemannZeta_eulerProduct_exp_log (by linarith),
    norm_tsum_neg_log_one_sub_prime_cpow_le hs⟩

/-- **Littlewood's bound**. Under the Riemann Hypothesis, for every fixed `1 / 2 < σ ≤ 1` and
every `ε > 0` there is a constant `C > 0` such that `‖ζ(σ + t * I)‖ ≤ C * t ^ ε` for all
`t ≥ 3`. -/
theorem exists_norm_riemannZeta_le_mul_rpow_of_half_lt (hRH : RiemannHypothesis) {σ ε : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ t → ‖riemannZeta (σ + t * I)‖ ≤ C * t ^ ε :=
  exists_norm_le_mul_rpow_of_half_lt zero_le_one (by norm_num)
    differentiableAt_riemannZeta_of_one_le_im norm_riemannZeta_le_mul_im_rpow
    (fun _ hre him => riemannZeta_ne_zero_of_half_lt_re_of_im_pos hRH hre (by linarith))
    exists_exp_eq_riemannZeta hσ hσ1 hε

end Lindelof

open Lindelof in
/-- **Littlewood's theorem**: the Riemann Hypothesis implies the Lindelöf Hypothesis, i.e.
`ζ(1 / 2 + t * I) = O(t ^ ε)` as `t → +∞` for every `ε > 0`. -/
theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε := by
  exact isBigO_rpow_of_ne_zero zero_le_one (by norm_num)
    differentiableAt_riemannZeta_of_one_le_im norm_riemannZeta_le_mul_im_rpow
    (fun _ hre him => riemannZeta_ne_zero_of_half_lt_re_of_im_pos hRH hre (by linarith))
    exists_exp_eq_riemannZeta

/-- The same bound as `t → -∞`, by the symmetry `ζ(conj s) = conj (ζ s)`. -/
theorem lindelof_atBot_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atBot] fun t : ℝ => |t| ^ ε := by
  intro ε hε
  have h := (lindelof_of_riemannHypothesis hRH ε hε).comp_tendsto Filter.tendsto_neg_atBot_atTop
  have h1 : ∀ t : ℝ, ‖riemannZeta (1 / 2 + ((-t : ℝ) : ℂ) * I)‖ =
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ := by
    intro t
    have e : (1 / 2 + ((-t : ℝ) : ℂ) * I) = (starRingEnd ℂ) (1 / 2 + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, riemannZeta_conj, Complex.norm_conj]
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  filter_upwards [hc, Filter.eventually_lt_atBot 0] with t ht ht0
  simp only [Function.comp_apply] at ht
  rw [← h1 t, abs_of_neg ht0]
  exact ht
