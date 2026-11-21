import RHImpliesLindelof.Dirichlet.Main
import RHImpliesLindelof.Dirichlet.UniformGrowth
import RHImpliesLindelof.Dirichlet.UniformLog

/-!
# Conductor-uniform bound for Dirichlet `L`-functions to the right of the critical line

Assuming that `L(s, χ)` does not vanish on `1 / 2 < re s`, we prove that for fixed
`1 / 2 < σ ≤ 1` and `η > 0`,
`‖L(σ + t * I, χ)‖ ≤ C * (N * (|t| + 2)) ^ η` for all real `t`, with a constant `C` depending
only on `σ` and `η` — not on the modulus `N`, the nontrivial character `χ`, or `t`.

The proof applies `Lindelof.exists_norm_le_mul_exp_of_ne_zero` on the disc of centre `2 + t * I`,
using the uniform growth bound `DirichletCharacter.norm_LFunction_le_of_dist_lt` and the bound
`DirichletCharacter.norm_tsum_neg_log_one_sub_mul_prime_cpow_le` for the Euler-product
logarithm, which is independent of `χ`.

## Main results

* `DirichletCharacter.exists_norm_LFunction_le_mul_rpow_of_half_lt`: the bound described above.
-/

open Complex Metric

namespace DirichletCharacter

/-- **Conductor-uniform Littlewood bound**. For fixed `1 / 2 < σ ≤ 1` and `η > 0` there is a
constant `C` such that for every modulus `N` and every nontrivial Dirichlet character `χ`
modulo `N` whose `L`-function does not vanish on `1 / 2 < re s`, we have
`‖L(σ + t * I, χ)‖ ≤ C * (N * (|t| + 2)) ^ η` for all real `t`. -/
theorem exists_norm_LFunction_le_mul_rpow_of_half_lt {σ η : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1)
    (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (∀ s : ℂ, 1 / 2 < s.re → LFunction χ s ≠ 0) →
      ∀ t : ℝ, ‖LFunction χ (σ + t * I)‖ ≤ C * ((N : ℝ) * (|t| + 2)) ^ η := by
  set δ : ℝ := (σ - 1 / 2) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 / 4 := by rw [hδ]; linarith
  obtain ⟨C, hC, hmain⟩ := Lindelof.exists_norm_le_mul_exp_of_ne_zero (r := 2 - σ)
    (K := 3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)) hδ0 hδ1 (by linarith)
    (by rw [hδ]; linarith) hη
  refine ⟨C * 10 ^ η, by positivity, fun N _ χ hχ hGRH t => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  set Q : ℝ := N * (|t| + 2) with hQ
  have hQ2 : 2 ≤ Q := by nlinarith [abs_nonneg t]
  have hQ0 : 0 < Q := by linarith
  have hM : 1 ≤ Real.log (10 * Q) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_three]
  have hre : ∀ (ρ : ℝ) (s : ℂ), s ∈ ball (2 + t * I : ℂ) ρ → 2 - ρ < s.re := by
    intro ρ s hs
    have hs' : ‖s - (2 + t * I)‖ < ρ := by simpa [dist_eq_norm] using hs
    have h1 := (abs_re_le_norm (s - (2 + t * I))).trans_lt hs'
    simp only [sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, re_ofNat, mul_zero,
      mul_one, sub_zero, add_zero] at h1
    rw [abs_lt] at h1
    linarith [h1.1]
  have hdist : dist ((σ : ℂ) + t * I) (2 + t * I) = 2 - σ := by
    rw [Complex.dist_eq]
    have : (σ : ℂ) + t * I - (2 + t * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have key := hmain (LFunction χ) (2 + t * I) (Real.log (10 * Q)) hM
    (fun s _ => (differentiable_LFunction hχ s).differentiableWithinAt)
    (fun s hs => hGRH s (by linarith [hre _ s hs]))
    (fun s hs => by
      rw [Real.exp_log (by positivity)]
      exact norm_LFunction_le_of_dist_lt hχ (lt_of_lt_of_le (mem_ball.1 hs) (by linarith))
        (by linarith [hre _ s hs]))
    (fun s hs => by
      have hs32 : 3 / 2 ≤ s.re := by linarith [hre _ s hs]
      have hs1 : 1 < s.re := by linarith
      refine ⟨_, ?_, norm_tsum_neg_log_one_sub_mul_prime_cpow_le χ hs32⟩
      rw [LFunction_eq_LSeries χ hs1]
      exact LSeries_eulerProduct_exp_log χ hs1)
    (σ + t * I) (mem_sphere.2 hdist)
  have hexp : Real.exp (η * Real.log (10 * Q)) = 10 ^ η * Q ^ η := by
    rw [← Real.mul_rpow (by norm_num) hQ0.le, Real.rpow_def_of_pos (by positivity), mul_comm]
  rw [hexp, ← mul_assoc] at key
  exact key

end DirichletCharacter
