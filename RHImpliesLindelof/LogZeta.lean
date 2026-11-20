import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The Euler-product logarithm of `ζ` and its non-vanishing under the Riemann Hypothesis

This file collects the `ζ`-specific inputs of the abstract Lindelöf bound
`Lindelof.isBigO_rpow_of_ne_zero`, apart from the growth bound of
`RHImpliesLindelof/Growth.lean`.

## Main results

* `Lindelof.norm_tsum_neg_log_one_sub_prime_cpow_le`: a uniform bound for the Euler-product
  logarithm of `ζ` on `3 / 2 ≤ re s`.
* `Lindelof.riemannZeta_ne_zero_of_half_lt_re_of_im_pos`: under RH, `ζ` does not vanish on
  `1 / 2 < re s`, `0 < im s`.
-/

open Complex

namespace Lindelof

/-- Uniform bound for the Euler-product logarithm of `ζ` on `3 / 2 ≤ re s`. -/
lemma norm_tsum_neg_log_one_sub_prime_cpow_le {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖ ≤
      3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
  have hsum : Summable (fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine tsum_of_norm_bounded (hsum.hasSum.mul_left (3 / 2)) fun p ↦ ?_
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt.le
  have h1 : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [norm_natCast_cpow_of_pos p.prop.pos]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    simp only [neg_re]; linarith
  have h2 : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    Complex.norm_prime_cpow_le_one_half p (by linarith)
  have h3 := Complex.norm_log_one_add_half_le_self (z := -(((p : ℕ) : ℂ) ^ (-s)))
    (by simpa using h2)
  rw [norm_neg, sub_eq_add_neg]
  refine h3.trans ?_
  rw [norm_neg]
  gcongr

/-- Under the Riemann Hypothesis, `ζ` does not vanish at points with `1 / 2 < re s` and
`0 < im s`. -/
lemma riemannZeta_ne_zero_of_half_lt_re_of_im_pos (hRH : RiemannHypothesis) {s : ℂ}
    (hre : 1 / 2 < s.re) (him : 0 < s.im) : riemannZeta s ≠ 0 := by
  intro h0
  have h := hRH s h0 (by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp at this
    linarith) (by
    rintro rfl
    simp at him)
  linarith

end Lindelof
