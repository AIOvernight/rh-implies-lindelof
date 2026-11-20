import Mathlib.Analysis.Calculus.Deriv.Star
import RHImpliesLindelof.Dirichlet.Growth
import RHImpliesLindelof.General

/-!
# Nonvanishing to the right of the critical line implies Lindelöf for Dirichlet `L`-functions

Let `χ` be a nontrivial Dirichlet character modulo `N`. Assuming that `L(s, χ)` does not vanish
on `1 / 2 < re s` (the Generalized Riemann Hypothesis for `χ`), we prove the Lindelöf bound in
the `t`-aspect: `L(1 / 2 + t * I, χ) = O(|t| ^ ε)` for every `ε > 0`, the implied constant
depending on `χ` and `ε`.

The proof applies the abstract statement `Lindelof.isBigO_rpow_of_ne_zero` to `L(·, χ)`, using
the linear growth bound `DirichletCharacter.norm_LFunction_le_mul_abs_im` and the Euler product.
The case `t → -∞` follows by applying the same abstract statement to `s ↦ conj (L(conj s, χ))`.

## Main results

* `DirichletCharacter.norm_tsum_neg_log_one_sub_mul_prime_cpow_le`: a uniform bound for the
  Euler-product logarithm of `L(s, χ)` on `3 / 2 ≤ re s`.
* `DirichletCharacter.lindelof_of_LFunction_ne_zero`: `L(1 / 2 + t * I, χ) = O(t ^ ε)` as
  `t → +∞`.
* `DirichletCharacter.lindelof_atBot_of_LFunction_ne_zero`: `L(1 / 2 + t * I, χ) = O(|t| ^ ε)`
  as `t → -∞`.
-/

open Complex

namespace DirichletCharacter

variable {N : ℕ}

/-- Uniform bound for the Euler-product logarithm of `L(s, χ)` on `3 / 2 ≤ re s`. -/
lemma norm_tsum_neg_log_one_sub_mul_prime_cpow_le (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 3 / 2 ≤ s.re) :
    ‖∑' p : Nat.Primes, -Complex.log (1 - χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s))‖ ≤
      3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
  have hsum : Summable (fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine tsum_of_norm_bounded (hsum.hasSum.mul_left (3 / 2)) fun p ↦ ?_
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt.le
  have hmul : ‖χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ‖((p : ℕ) : ℂ) ^ (-s)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have h1 : ‖χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤
      ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
    refine hmul.trans ?_
    rw [norm_natCast_cpow_of_pos p.prop.pos]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    simp only [neg_re]; linarith
  have h2 : ‖χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    hmul.trans (Complex.norm_prime_cpow_le_one_half p (by linarith))
  have h3 := Complex.norm_log_one_add_half_le_self
    (z := -(χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s))) (by simpa using h2)
  rw [norm_neg, sub_eq_add_neg]
  refine h3.trans ?_
  rw [norm_neg]
  gcongr

variable [NeZero N]

/-- **Lindelöf bound for Dirichlet `L`-functions under GRH**. Let `χ` be a nontrivial Dirichlet
character whose `L`-function does not vanish on `1 / 2 < re s`. Then
`L(1 / 2 + t * I, χ) = O(t ^ ε)` as `t → +∞` for every `ε > 0`. -/
theorem lindelof_of_LFunction_ne_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hGRH : ∀ s : ℂ, 1 / 2 < s.re → LFunction χ s ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => LFunction χ (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε := by
  refine Lindelof.isBigO_rpow_of_ne_zero (A := 1) (C₀ := 20 * (N + 1)) zero_le_one
    (by positivity) (fun s _ _ => differentiable_LFunction hχ s) (fun s h1 h2 h3 => ?_)
    (fun s hs _ => hGRH s hs)
    (fun s hs _ => ⟨_, ?_, norm_tsum_neg_log_one_sub_mul_prime_cpow_le χ hs⟩)
  · have h0 : 0 ≤ s.im := zero_le_one.trans h3
    simpa only [Real.rpow_one, abs_of_nonneg h0] using
      norm_LFunction_le_mul_abs_im hχ h1 h2 (by rwa [abs_of_nonneg h0])
  · have hs1 : 1 < s.re := by linarith
    rw [LFunction_eq_LSeries χ hs1]
    exact LSeries_eulerProduct_exp_log χ hs1

/-- The Lindelöf bound for Dirichlet `L`-functions under GRH, as `t → -∞`: if `χ` is a
nontrivial Dirichlet character whose `L`-function does not vanish on `1 / 2 < re s`, then
`L(1 / 2 + t * I, χ) = O(|t| ^ ε)` as `t → -∞` for every `ε > 0`. -/
theorem lindelof_atBot_of_LFunction_ne_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hGRH : ∀ s : ℂ, 1 / 2 < s.re → LFunction χ s ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => LFunction χ (1 / 2 + t * I)) =O[Filter.atBot] fun t : ℝ => |t| ^ ε := by
  intro ε hε
  -- the reflected function `s ↦ conj (L(conj s, χ))` satisfies the same hypotheses
  have hF : (fun t : ℝ => (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) (1 / 2 + t * I))))
      =O[Filter.atTop] fun t : ℝ => t ^ ε := by
    refine Lindelof.isBigO_rpow_of_ne_zero
      (F := fun s => (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) s))) (A := 1)
      (C₀ := 20 * (N + 1)) zero_le_one (by positivity)
      (fun s _ _ => differentiableAt_conj_conj_iff.2 (differentiable_LFunction hχ _))
      (fun s h1 h2 h3 => ?_)
      (fun s hs _ => ?_) (fun s hs _ => ⟨(starRingEnd ℂ) _, ?_,
        (norm_conj _).le.trans
          (norm_tsum_neg_log_one_sub_mul_prime_cpow_le χ (s := (starRingEnd ℂ) s) hs)⟩) ε hε
    · have h0 : 0 ≤ s.im := zero_le_one.trans h3
      have := norm_LFunction_le_mul_abs_im hχ (s := (starRingEnd ℂ) s) h1 h2
        (by simpa [abs_of_nonneg h0] using h3)
      simpa [abs_of_nonneg h0] using this
    · simpa using hGRH ((starRingEnd ℂ) s) (by simpa using hs)
    · have hs1 : 1 < ((starRingEnd ℂ) s).re := by rw [conj_re]; linarith
      rw [Complex.exp_conj, LSeries_eulerProduct_exp_log χ hs1, LFunction_eq_LSeries χ hs1]
  have h := hF.comp_tendsto Filter.tendsto_neg_atBot_atTop
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  filter_upwards [hc, Filter.eventually_lt_atBot 0] with t ht ht0
  simp only [Function.comp_apply, norm_conj] at ht
  have e : (starRingEnd ℂ) (1 / 2 + ((-t : ℝ) : ℂ) * I) = 1 / 2 + (t : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [e] at ht
  rwa [abs_of_neg ht0]

end DirichletCharacter
