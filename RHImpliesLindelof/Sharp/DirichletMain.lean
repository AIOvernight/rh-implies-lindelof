import RHImpliesLindelof.Dirichlet.Main
import RHImpliesLindelof.Sharp.DirichletGeneral

/-!
# Littlewood's sharper bound for Dirichlet `L`-functions on the critical line, under GRH

Let `χ` be a nontrivial Dirichlet character modulo `N`. Assuming that `L(s, χ)` does not vanish
on `1 / 2 < re s` (the Generalized Riemann Hypothesis for `χ`), we prove
`‖L(1 / 2 + t * I, χ)‖ ≤ exp (C * log |t| / log (log |t|))` for `|t| ≥ 100`, the constant `C`
depending on `χ`.

The proof applies the abstract statement `Lindelof.exists_norm_le_exp_log_div_log_log_of_ne_zero`
to `L(·, χ)`, using the linear growth bound `DirichletCharacter.norm_LFunction_le_mul_abs_im`
and the Euler product. Negative `t` are handled by applying the same abstract statement to
`s ↦ conj (L(conj s, χ))`, so no hypothesis on the conjugate character is needed.

## Main results

* `DirichletCharacter.exp_neg_le_norm_LFunction`: two-sided bound for `‖L(s, χ)‖` on
  `3 / 2 ≤ re s`.
* `DirichletCharacter.exists_forall_norm_LFunction_le_exp_log_div_log_log`: the bound for all
  real `t` with `100 ≤ |t|`.
* `DirichletCharacter.exists_norm_LFunction_le_exp_log_div_log_log`: the bound as `t → +∞`.
* `DirichletCharacter.exists_norm_LFunction_le_exp_log_div_log_log_atBot`: the bound as
  `t → -∞`.
-/

open Complex

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- Two-sided bound for `‖L(s, χ)‖` on `3 / 2 ≤ re s`, from the Euler product. -/
lemma exp_neg_le_norm_LFunction (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    Real.exp (-(3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ))) ≤ ‖LFunction χ s‖ ∧
      ‖LFunction χ s‖ ≤ Real.exp (3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)) := by
  have hs1 : 1 < s.re := by linarith
  have h := norm_tsum_neg_log_one_sub_mul_prime_cpow_le χ hs
  have h1 := abs_re_le_norm
    (∑' p : Nat.Primes, -Complex.log (1 - χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s)))
  rw [LFunction_eq_LSeries χ hs1, ← LSeries_eulerProduct_exp_log χ hs1, Complex.norm_exp]
  rw [abs_le] at h1
  exact ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_exp.2 (by linarith)⟩

/-- **Littlewood's bound for Dirichlet `L`-functions under GRH**, uniform version. Let `χ` be a
nontrivial Dirichlet character whose `L`-function does not vanish on `1 / 2 < re s`. Then
there is a constant `C` such that
`‖L(1 / 2 + t * I, χ)‖ ≤ exp (C * log |t| / log (log |t|))` for all real `t` with
`100 ≤ |t|`. -/
theorem exists_forall_norm_LFunction_le_exp_log_div_log_log (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hGRH : ∀ s : ℂ, 1 / 2 < s.re → LFunction χ s ≠ 0) :
    ∃ C : ℝ, ∀ t : ℝ, 100 ≤ |t| →
      ‖LFunction χ (1 / 2 + t * I)‖ ≤
        Real.exp (C * Real.log |t| / Real.log (Real.log |t|)) := by
  obtain ⟨C₁, h₁⟩ := Lindelof.exists_norm_le_exp_log_div_log_log_of_ne_zero
    (F := LFunction χ) (A := 1) (C₀ := 20 * (N + 1)) zero_le_one (by positivity)
    (fun s _ _ ↦ differentiable_LFunction hχ s) (fun s h1 h2 h3 ↦ by
      have h0 : 0 ≤ s.im := zero_le_one.trans h3
      simpa only [Real.rpow_one, abs_of_nonneg h0] using
        norm_LFunction_le_mul_abs_im hχ h1 h2 (by rwa [abs_of_nonneg h0]))
    (fun s hs _ ↦ hGRH s hs) (fun s hs _ ↦ exp_neg_le_norm_LFunction χ hs)
  -- the reflected function `s ↦ conj (L(conj s, χ))` satisfies the same hypotheses
  obtain ⟨C₂, h₂⟩ := Lindelof.exists_norm_le_exp_log_div_log_log_of_ne_zero
    (F := fun s ↦ (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) s))) (A := 1)
    (C₀ := 20 * (N + 1)) zero_le_one (by positivity)
    (fun s _ _ ↦ differentiableAt_conj_conj_iff.2 (differentiable_LFunction hχ _))
    (fun s h1 h2 h3 ↦ by
      have h0 : 0 ≤ s.im := zero_le_one.trans h3
      have := norm_LFunction_le_mul_abs_im hχ (s := (starRingEnd ℂ) s) h1 h2
        (by simpa [abs_of_nonneg h0] using h3)
      simpa [abs_of_nonneg h0] using this)
    (fun s hs _ ↦ by simpa using hGRH ((starRingEnd ℂ) s) (by simpa using hs))
    (fun s hs _ ↦ by
      simpa only [norm_conj] using exp_neg_le_norm_LFunction χ (s := (starRingEnd ℂ) s) hs)
  refine ⟨max C₁ C₂, fun t ht ↦ ?_⟩
  have hlog : 1 < Real.log |t| := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact Real.exp_one_lt_three.trans (by linarith)
  have hmono : ∀ C : ℝ, C ≤ max C₁ C₂ →
      Real.exp (C * Real.log |t| / Real.log (Real.log |t|)) ≤
        Real.exp (max C₁ C₂ * Real.log |t| / Real.log (Real.log |t|)) := by
    intro C hC
    have hll : 0 < Real.log (Real.log |t|) := Real.log_pos hlog
    gcongr
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ⊢
    exact (h₁ t ht).trans (by simpa only [abs_of_nonneg h0] using hmono C₁ (le_max_left _ _))
  · rw [abs_of_nonpos h0] at ht
    have h := h₂ (-t) ht
    have e : (starRingEnd ℂ) (1 / 2 + ((-t : ℝ) : ℂ) * I) = 1 / 2 + (t : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [norm_conj, e] at h
    exact h.trans (by simpa only [abs_of_nonpos h0] using hmono C₂ (le_max_right _ _))

end DirichletCharacter

/-- **Littlewood's bound for Dirichlet `L`-functions under GRH**. Let `χ` be a nontrivial
Dirichlet character whose `L`-function does not vanish on `1 / 2 < re s`. Then there is a
constant `C` such that `‖L(1 / 2 + t * I, χ)‖ ≤ exp (C * log t / log (log t))` for all
sufficiently large `t`. -/
theorem DirichletCharacter.exists_norm_LFunction_le_exp_log_div_log_log {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hGRH : ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in Filter.atTop,
      ‖DirichletCharacter.LFunction χ (1 / 2 + t * I)‖ ≤
        Real.exp (C * Real.log t / Real.log (Real.log t)) := by
  obtain ⟨C, hC⟩ := χ.exists_forall_norm_LFunction_le_exp_log_div_log_log hχ hGRH
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (100 : ℝ)] with t ht
  have h0 : 0 ≤ t := by linarith
  simpa only [abs_of_nonneg h0] using hC t (by rwa [abs_of_nonneg h0])

/-- Littlewood's bound for Dirichlet `L`-functions under GRH, as `t → -∞`: if `χ` is a
nontrivial Dirichlet character whose `L`-function does not vanish on `1 / 2 < re s`, then there
is a constant `C` such that `‖L(1 / 2 + t * I, χ)‖ ≤ exp (C * log |t| / log (log |t|))` for all
sufficiently negative `t`. No hypothesis on the conjugate character is needed. -/
theorem DirichletCharacter.exists_norm_LFunction_le_exp_log_div_log_log_atBot {N : ℕ}
    [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hGRH : ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in Filter.atBot,
      ‖DirichletCharacter.LFunction χ (1 / 2 + t * I)‖ ≤
        Real.exp (C * Real.log |t| / Real.log (Real.log |t|)) := by
  obtain ⟨C, hC⟩ := χ.exists_forall_norm_LFunction_le_exp_log_div_log_log hχ hGRH
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_le_atBot (-100 : ℝ)] with t ht
  exact hC t (by rw [abs_of_nonpos (by linarith)]; linarith)
