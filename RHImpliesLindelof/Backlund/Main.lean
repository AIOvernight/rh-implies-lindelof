import RHImpliesLindelof.Backlund.Local

/-!
# Backlund's reformulation of the Lindelöf hypothesis

We prove the classical equivalence (Backlund; Titchmarsh, *The theory of the Riemann
zeta-function*, §13.5) between the Lindelöf hypothesis `ζ(1 / 2 + t * I) = O(t ^ ε)` and the
statement that, for every `σ > 1 / 2`, the number of zeros `ρ` of `ζ` with `σ < re ρ` and
`T < im ρ ≤ T + 1`, counted with multiplicity, is `o(log T)` as `T → ∞`. This is an unconditional
equivalence between two open statements.

The main theorems are stated using Mathlib notions only: the zeros are counted by the finite
sum `∑ᶠ ρ ∈ {ρ | ζ ρ = 0 ∧ σ < re ρ ∧ T < im ρ ∧ im ρ ≤ T + 1}, (analyticOrderAt ζ ρ).toNat`
(which is `Lindelof.zetaZeroCount σ T` by definition; the set is finite for large `T`, see
`Lindelof.exists_finite_zetaZeroBox`).

## Main results

* `riemannZeta_zeros_isLittleO_log_of_lindelof`: Lindelöf implies the zero-count bounds.
* `lindelof_of_riemannZeta_zeros_isLittleO_log`: the zero-count bounds imply Lindelöf.
* `lindelof_iff_riemannZeta_zeros_isLittleO_log`: the equivalence.

## Auxiliary results

* `Lindelof.exists_norm_riemannZeta_le_mul_rpow_of_zetaZeroCount_isLittleO`: if the zero counts
  are `o(log T)`, then `ζ(σ + t * I) = O(t ^ η)` for all `1 / 2 < σ ≤ 1` and `η > 0`.
-/

open Complex

namespace Lindelof

/-- If for every `σ > 1 / 2` the number of zeros of `ζ` with `σ < re ρ`, `T < im ρ ≤ T + 1` is
`o(log T)`, then for every `1 / 2 < σ ≤ 1` and `η > 0` there is `C > 0` with
`‖ζ(σ + t * I)‖ ≤ C * t ^ η` for all `t ≥ 1`. -/
theorem exists_norm_riemannZeta_le_mul_rpow_of_zetaZeroCount_isLittleO
    (h : ∀ σ : ℝ, 1 / 2 < σ →
      (fun T : ℝ => (zetaZeroCount σ T : ℝ)) =o[Filter.atTop] Real.log)
    {σ η : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖riemannZeta (σ + t * I)‖ ≤ C * t ^ η := by
  set δ : ℝ := (σ - 1 / 2) / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ8 : δ ≤ 1 / 8 := by rw [hδ]; linarith
  have hσeq : σ = 1 / 2 + 4 * δ := by rw [hδ]; ring
  obtain ⟨C, a, t₀, hC, ha0, ha1, hloc⟩ :=
    exists_norm_riemannZeta_le_exp_of_zetaZeroCount hδ0 hδ8
  have h1a : 0 < 1 - a := by linarith
  -- the zero counts will be at most `ε * log t`
  set ε : ℝ := min (min 1 (η / 4)) ((η / (4 * C)) ^ (1 / (1 - a))) with hε
  have hε0 : 0 < ε :=
    lt_min (lt_min one_pos (by positivity)) (Real.rpow_pos_of_pos (by positivity) _)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεη : ε ≤ η / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hεa : ε ^ (1 - a) ≤ η / (4 * C) := by
    have := Real.rpow_le_rpow hε0.le
      (min_le_right _ _ : ε ≤ (η / (4 * C)) ^ (1 / (1 - a))) h1a.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel h1a.ne', Real.rpow_one] at this
  have hsmall := (h (1 / 2 + δ) (by linarith)).def (by positivity : 0 < ε / 8)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hsmall
  set t₁ : ℝ := max (max t₀ (T₁ + 2)) (max 3 (Real.exp (1 / ε))) with ht₁
  have ht₁3 : 3 ≤ t₁ := (le_max_left _ _).trans (le_max_right _ _)
  have key : ∀ t : ℝ, t₁ ≤ t → ‖riemannZeta (σ + t * I)‖ ≤ t ^ η := by
    intro t ht
    have ht0' : t₀ ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
    have htT : T₁ + 2 ≤ t := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
    have ht3 : 3 ≤ t := ht₁3.trans ht
    have hte : Real.exp (1 / ε) ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
    have ht0 : 0 < t := by linarith
    set L : ℝ := Real.log t with hL
    have hLε : 1 / ε ≤ L := by
      rw [hL, Real.le_log_iff_exp_le ht0]
      exact hte
    have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hLε
    have hεL : 1 ≤ ε * L := by
      rw [div_le_iff₀ hε0] at hLε
      linarith
    obtain ⟨n, hn, hbound⟩ := hloc t ht0'
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnL : (n : ℝ) ≤ ε * L := by
      have hterm : ∀ j ∈ Finset.range 4,
          (zetaZeroCount (1 / 2 + δ) (t - 2 + j) : ℝ) ≤ ε / 8 * (2 * L) := by
        intro j hj
        have hj3 : (j : ℝ) ≤ 3 := by
          have := Finset.mem_range.1 hj
          exact_mod_cast Nat.lt_succ_iff.1 this
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have hT := hT₁ (t - 2 + j) (by linarith)
        rw [Real.norm_natCast, Real.norm_of_nonneg (Real.log_nonneg (by linarith))] at hT
        refine hT.trans ?_
        have hlog : Real.log (t - 2 + j) ≤ 2 * L := by
          have h2 : Real.log (t - 2 + j) ≤ Real.log (t ^ 2) :=
            Real.log_le_log (by linarith) (by nlinarith)
          rwa [Real.log_pow, Nat.cast_ofNat] at h2
        gcongr
      have hsum : ((∑ j ∈ Finset.range 4, zetaZeroCount (1 / 2 + δ) (t - 2 + j) : ℕ) : ℝ) ≤
          ε * L := by
        push_cast
        calc ∑ j ∈ Finset.range 4, (zetaZeroCount (1 / 2 + δ) (t - 2 + j) : ℝ)
            ≤ ∑ _j ∈ Finset.range 4, ε / 8 * (2 * L) := Finset.sum_le_sum hterm
          _ = ε * L := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
      exact (Nat.cast_le.2 hn).trans hsum
    have hX : (C * (1 + n)) ^ (1 - a) * (C * (L + n)) ^ a + 2 * n ≤ η * L := by
      have hx : 0 < 2 * C * L := by positivity
      have hb1 : C * (1 + n) ≤ 2 * C * L * ε := by
        have : C * (1 + n) ≤ C * (2 * (ε * L)) := mul_le_mul_of_nonneg_left (by linarith) hC.le
        linarith
      have hb2 : C * (L + n) ≤ 2 * C * L := by
        have hεL' : ε * L ≤ L := by nlinarith
        have : C * (L + n) ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hC.le
        linarith
      have hp1 : (C * (1 + n)) ^ (1 - a) ≤ (2 * C * L * ε) ^ (1 - a) :=
        Real.rpow_le_rpow (by positivity) hb1 h1a.le
      have hp2 : (C * (L + n)) ^ a ≤ (2 * C * L) ^ a :=
        Real.rpow_le_rpow (by positivity) hb2 ha0.le
      have hprod : (2 * C * L * ε) ^ (1 - a) * (2 * C * L) ^ a = 2 * C * L * ε ^ (1 - a) := by
        rw [Real.mul_rpow hx.le hε0.le, mul_right_comm, ← Real.rpow_add hx]
        simp
      have hlast : 2 * C * L * ε ^ (1 - a) ≤ η / 2 * L := by
        have := mul_le_mul_of_nonneg_left hεa hx.le
        have e : 2 * C * L * (η / (4 * C)) = η / 2 * L := by
          field_simp
          ring
        linarith
      have hmul := mul_le_mul hp1 hp2 (by positivity) (by positivity)
      have h2n : 2 * (n : ℝ) ≤ η / 2 * L := by nlinarith
      linarith
    have hcast : (σ : ℂ) = ((1 / 2 + 4 * δ : ℝ) : ℂ) := by rw [← hσeq]
    rw [hcast]
    refine hbound.trans ?_
    rw [Real.rpow_def_of_pos ht0, Real.exp_le_exp]
    linarith [mul_comm η L]
  refine ⟨25 * t₁, by positivity, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have hpow : (1 : ℝ) ≤ t ^ η := Real.one_le_rpow ht hη.le
  rcases le_or_gt t₁ t with h1 | h1
  · exact (key t h1).trans (le_mul_of_one_le_left (by positivity) (by linarith))
  · have hgrow := norm_riemannZeta_le_mul_abs_im (s := σ + t * I) (by simp; linarith)
      (by simp; linarith) (by simpa [abs_of_nonneg ht0] using ht)
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rw [him, abs_of_nonneg ht0] at hgrow
    calc ‖riemannZeta (σ + t * I)‖ ≤ 25 * t := hgrow
      _ ≤ 25 * t₁ * 1 := by linarith
      _ ≤ 25 * t₁ * t ^ η := by gcongr

end Lindelof

/-- **The Lindelöf hypothesis implies Backlund's zero-count bounds**: if
`ζ(1 / 2 + t * I) = O(t ^ ε)` for every `ε > 0`, then for every `σ > 1 / 2` the number of zeros
`ρ` of `ζ` with `σ < re ρ` and `T < im ρ ≤ T + 1`, counted with multiplicity, is `o(log T)`. -/
theorem riemannZeta_zeros_isLittleO_log_of_lindelof
    (h : ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε) :
    ∀ σ : ℝ, 1 / 2 < σ →
      (fun T : ℝ =>
        ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ T < ρ.im ∧ ρ.im ≤ T + 1},
          (analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℝ)) =o[Filter.atTop] Real.log :=
  fun _ hσ => Lindelof.zetaZeroCount_isLittleO_log_of_lindelof h hσ

/-- **Backlund's zero-count bounds imply the Lindelöf hypothesis**: if for every `σ > 1 / 2`
the number of zeros `ρ` of `ζ` with `σ < re ρ` and `T < im ρ ≤ T + 1`, counted with
multiplicity, is `o(log T)`, then `ζ(1 / 2 + t * I) = O(t ^ ε)` for every `ε > 0`. -/
theorem lindelof_of_riemannZeta_zeros_isLittleO_log
    (h : ∀ σ : ℝ, 1 / 2 < σ →
      (fun T : ℝ =>
        ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ T < ρ.im ∧ ρ.im ≤ T + 1},
          (analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℝ)) =o[Filter.atTop] Real.log) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε :=
  Lindelof.isBigO_riemannZeta_of_forall_half_lt fun _ _ hσ hσ1 hη =>
    Lindelof.exists_norm_riemannZeta_le_mul_rpow_of_zetaZeroCount_isLittleO h hσ hσ1 hη

/-- **Backlund's reformulation of the Lindelöf hypothesis**: `ζ(1 / 2 + t * I) = O(t ^ ε)` for
every `ε > 0` if and only if, for every `σ > 1 / 2`, the number of zeros `ρ` of `ζ` with
`σ < re ρ` and `T < im ρ ≤ T + 1`, counted with multiplicity, is `o(log T)` as `T → ∞`. -/
theorem lindelof_iff_riemannZeta_zeros_isLittleO_log :
    (∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε) ↔
    ∀ σ : ℝ, 1 / 2 < σ →
      (fun T : ℝ =>
        ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ T < ρ.im ∧ ρ.im ≤ T + 1},
          (analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℝ)) =o[Filter.atTop] Real.log :=
  ⟨riemannZeta_zeros_isLittleO_log_of_lindelof, lindelof_of_riemannZeta_zeros_isLittleO_log⟩
