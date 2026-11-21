import RHImpliesLindelof.Dirichlet.UniformHalfLt

/-!
# The conductor-uniform Lindelöf bound for Dirichlet `L`-functions on the critical line

Assuming that `L(s, χ)` does not vanish on `1 / 2 < re s`, we prove the Lindelöf bound on the
critical line uniformly in the modulus, the character and the height: for every `ε > 0` there is
a constant `C` depending only on `ε` such that
`‖L(1 / 2 + t * I, χ)‖ ≤ C * (N * (|t| + 2)) ^ ε` for every nontrivial character `χ` modulo `N`
and every real `t`.

The passage from the line `re s = 1 / 2 + θ` (where the bound is
`DirichletCharacter.exists_norm_LFunction_le_mul_rpow_of_half_lt`) to the critical line is a
convexity argument localised at the target height `t₀`: with `Q = N * (|t₀| + 2)` treated as a
constant, the function `f z * exp (-(1 + κ * (z - a)) * log Q) / (z - a + 1 - t₀ * I)` is bounded
in the strip `a ≤ re z ≤ b`, and bounded by absolute constants on its two edges, so that
Hadamard's three-lines theorem applies on the whole strip.

## Main results

* `Lindelof.norm_le_mul_rpow_interp_of_vertical_strip`: the localised convexity bound, with an
  explicit constant.
* `DirichletCharacter.exists_norm_LFunction_le_mul_rpow_uniform`: the conductor-uniform Lindelöf
  bound on the critical line.
-/

open Complex

namespace Lindelof

/-- **Convexity bound localised at a height `t₀`, with explicit constant**. Let `f` be
differentiable and of linear growth in the strip `a ≤ re z ≤ b`. Let `Q ≥ 1` and `0 ≤ η ≤ 1`, and
suppose that `‖f z‖ ≤ A * Q * (1 + |im z - t₀|)` on the line `re z = a` and
`‖f z‖ ≤ B * Q ^ η * (1 + |im z - t₀|)` on the line `re z = b`. Then at every point `z₀` of the
strip at height `t₀`, `‖f z₀‖ ≤ 2 * max A B * (re z₀ - a + 1) * Q ^ e`, where the exponent
`e = 1 + (η - 1) / (b - a) * (re z₀ - a)` interpolates linearly between `1` and `η`. The
constant does not depend on `Q`, `t₀` or the growth constant `D`. -/
theorem norm_le_mul_rpow_interp_of_vertical_strip {f : ℂ → ℂ} {a b η Q A B D t₀ : ℝ}
    (hab : a < b) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hQ : 1 ≤ Q) (hA : 0 < A) (hB : 0 < B)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hgrow : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ D * (1 + ‖z‖))
    (hleft : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ A * Q * (1 + |z.im - t₀|))
    (hright : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ B * Q ^ η * (1 + |z.im - t₀|))
    {z₀ : ℂ} (h1 : a ≤ z₀.re) (h2 : z₀.re ≤ b) (h3 : z₀.im = t₀) :
    ‖f z₀‖ ≤ 2 * max A B * (z₀.re - a + 1) * Q ^ (1 + (η - 1) / (b - a) * (z₀.re - a)) := by
  have hQ0 : 0 < Q := by linarith
  set κ : ℝ := (η - 1) / (b - a) with hκ
  have hba : 0 < b - a := sub_pos.2 hab
  have hκ0 : κ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le
  have hκb : 1 + κ * (b - a) = η := by rw [hκ]; field_simp; ring
  set M : ℝ := 2 * max A B with hM
  have hMA : 2 * A ≤ M := by rw [hM]; linarith [le_max_left A B]
  have hMB : 2 * B ≤ M := by rw [hM]; linarith [le_max_right A B]
  have hMpos : 0 < M := by linarith
  set E : ℂ → ℂ := fun z => exp (-((1 + (κ : ℂ) * (z - a)) * (Real.log Q : ℂ))) with hE
  set den : ℂ → ℂ := fun z => z - a + 1 - t₀ * I with hden
  have hEnorm : ∀ z : ℂ, ‖E z‖ = Q ^ (-(1 + κ * (z.re - a))) := by
    intro z
    rw [hE, Complex.norm_exp, Real.rpow_def_of_pos hQ0]
    congr 1
    simp only [neg_re, mul_re, add_re, one_re, ofReal_re, sub_re, add_im, one_im, mul_im,
      ofReal_im, sub_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    ring
  have hdre : ∀ z : ℂ, (den z).re = z.re - a + 1 := fun z => by simp [hden]
  have hdim : ∀ z : ℂ, (den z).im = z.im - t₀ := fun z => by simp [hden]
  have hd1 : ∀ z : ℂ, a ≤ z.re → 1 ≤ ‖den z‖ := fun z hz =>
    le_trans (by rw [hdre]; linarith) (re_le_norm _)
  have hd2 : ∀ z : ℂ, a ≤ z.re → 1 + |z.im - t₀| ≤ 2 * ‖den z‖ := by
    intro z hz
    have := abs_im_le_norm (den z)
    rw [hdim] at this
    linarith [hd1 z hz]
  have hd0 : ∀ z : ℂ, a ≤ z.re → den z ≠ 0 := fun z hz =>
    norm_pos_iff.1 (zero_lt_one.trans_le (hd1 z hz))
  set G : ℂ → ℂ := fun z => f z * E z / den z with hG
  have hGnorm : ∀ z : ℂ, ‖G z‖ = ‖f z‖ * Q ^ (-(1 + κ * (z.re - a))) / ‖den z‖ := by
    intro z
    rw [hG, norm_div, norm_mul, hEnorm]
  -- the two edges
  have hGa : ∀ z ∈ re ⁻¹' {a}, ‖G z‖ ≤ M := by
    intro z hz
    have hz : z.re = a := hz
    have hdpos : 0 < ‖den z‖ := zero_lt_one.trans_le (hd1 z hz.ge)
    have hQinv : Q * Q ^ (-(1 : ℝ)) = 1 := by
      rw [Real.rpow_neg_one, mul_inv_cancel₀ hQ0.ne']
    rw [hGnorm, hz, sub_self, mul_zero, add_zero, div_le_iff₀ hdpos]
    calc ‖f z‖ * Q ^ (-(1 : ℝ)) ≤ A * Q * (1 + |z.im - t₀|) * Q ^ (-(1 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hleft z hz) (Real.rpow_nonneg hQ0.le _)
      _ = A * (1 + |z.im - t₀|) * (Q * Q ^ (-(1 : ℝ))) := by ring
      _ = A * (1 + |z.im - t₀|) := by rw [hQinv, mul_one]
      _ ≤ A * (2 * ‖den z‖) := mul_le_mul_of_nonneg_left (hd2 z hz.ge) hA.le
      _ ≤ M * ‖den z‖ := by nlinarith [mul_le_mul_of_nonneg_right hMA hdpos.le]
  have hGb : ∀ z ∈ re ⁻¹' {b}, ‖G z‖ ≤ M := by
    intro z hz
    have hz : z.re = b := hz
    have hdpos : 0 < ‖den z‖ := zero_lt_one.trans_le (hd1 z (hz ▸ hab.le))
    have hQinv : Q ^ η * Q ^ (-η) = 1 := by
      rw [← Real.rpow_add hQ0, add_neg_cancel, Real.rpow_zero]
    rw [hGnorm, hz, hκb, div_le_iff₀ hdpos]
    calc ‖f z‖ * Q ^ (-η) ≤ B * Q ^ η * (1 + |z.im - t₀|) * Q ^ (-η) :=
          mul_le_mul_of_nonneg_right (hright z hz) (Real.rpow_nonneg hQ0.le _)
      _ = B * (1 + |z.im - t₀|) * (Q ^ η * Q ^ (-η)) := by ring
      _ = B * (1 + |z.im - t₀|) := by rw [hQinv, mul_one]
      _ ≤ B * (2 * ‖den z‖) := mul_le_mul_of_nonneg_left (hd2 z (hz ▸ hab.le)) hB.le
      _ ≤ M * ‖den z‖ := by nlinarith [mul_le_mul_of_nonneg_right hMB hdpos.le]
  -- boundedness in the closed strip
  have hbdd : BddAbove ((norm ∘ G) '' HadamardThreeLines.verticalClosedStrip a b) := by
    refine ⟨|D| * (2 + ‖(a : ℂ) - 1 + t₀ * I‖), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hza : a ≤ z.re := hz.1
    have hzb : z.re ≤ b := hz.2
    have hdpos : 0 < ‖den z‖ := zero_lt_one.trans_le (hd1 z hza)
    have hQle : Q ^ (-(1 + κ * (z.re - a))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hQ
      nlinarith [mul_le_mul_of_nonpos_left (sub_le_sub_right hzb a) hκ0]
    have hnz : ‖z‖ ≤ ‖den z‖ + ‖(a : ℂ) - 1 + t₀ * I‖ := by
      have : z = den z + ((a : ℂ) - 1 + t₀ * I) := by rw [hden]; ring
      calc ‖z‖ = ‖den z + ((a : ℂ) - 1 + t₀ * I)‖ := by rw [← this]
        _ ≤ _ := norm_add_le _ _
    have hw : 0 ≤ ‖(a : ℂ) - 1 + t₀ * I‖ := norm_nonneg _
    have hfz : ‖f z‖ ≤ |D| * (1 + ‖z‖) :=
      (hgrow z hza hzb).trans (mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity))
    simp only [Function.comp_apply]
    rw [hGnorm, div_le_iff₀ hdpos]
    calc ‖f z‖ * Q ^ (-(1 + κ * (z.re - a))) ≤ ‖f z‖ * 1 :=
          mul_le_mul_of_nonneg_left hQle (norm_nonneg _)
      _ ≤ |D| * (1 + ‖z‖) := by rw [mul_one]; exact hfz
      _ ≤ |D| * ((2 + ‖(a : ℂ) - 1 + t₀ * I‖) * ‖den z‖) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg D)
          nlinarith [hd1 z hza]
      _ = |D| * (2 + ‖(a : ℂ) - 1 + t₀ * I‖) * ‖den z‖ := by ring
  -- holomorphy
  have hGd : DifferentiableOn ℂ G (HadamardThreeLines.verticalClosedStrip a b) := by
    intro z hz
    have hEd : DifferentiableAt ℂ E z := by rw [hE]; fun_prop
    have hdd : DifferentiableAt ℂ den z := by rw [hden]; fun_prop
    exact (((hd z hz.1 hz.2).mul hEd).div hdd (hd0 z hz.1)).differentiableWithinAt
  have hclosed : IsClosed (HadamardThreeLines.verticalClosedStrip a b) :=
    isClosed_Icc.preimage continuous_re
  have hsub : closure (HadamardThreeLines.verticalStrip a b) ⊆
      HadamardThreeLines.verticalClosedStrip a b :=
    hclosed.closure_subset_iff.mpr (fun w hw => ⟨hw.1.le, hw.2.le⟩)
  have hdc : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip a b) :=
    (hGd.mono hsub).diffContOnCl
  have key := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab
    (show z₀ ∈ HadamardThreeLines.verticalClosedStrip a b from ⟨h1, h2⟩) hdc hbdd hGa hGb
  rw [← Real.rpow_add hMpos, sub_add_cancel, Real.rpow_one] at key
  -- unfold `G` at `z₀`
  have hden₀ : ‖den z₀‖ = z₀.re - a + 1 := by
    have : den z₀ = ((z₀.re - a + 1 : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [hdre, ofReal_re]
      · rw [hdim, ofReal_im, h3, sub_self]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hdpos : 0 < z₀.re - a + 1 := by linarith
  have hQpos : 0 < Q ^ (1 + κ * (z₀.re - a)) := Real.rpow_pos_of_pos hQ0 _
  rw [hGnorm, hden₀, Real.rpow_neg hQ0.le, div_le_iff₀ hdpos, ← div_eq_mul_inv,
    div_le_iff₀ hQpos] at key
  exact key

end Lindelof

namespace DirichletCharacter

/-- **The conductor-uniform Lindelöf bound for Dirichlet `L`-functions under GRH**. For every
`ε > 0` there is a constant `C`, depending only on `ε`, such that for every modulus `N` and
every nontrivial Dirichlet character `χ` modulo `N` whose `L`-function does not vanish on
`1 / 2 < re s`, we have `‖L(1 / 2 + t * I, χ)‖ ≤ C * (N * (|t| + 2)) ^ ε` for all real `t`. -/
theorem exists_norm_LFunction_le_mul_rpow_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0) →
      ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (1 / 2 + t * I)‖ ≤
        C * ((N : ℝ) * (|t| + 2)) ^ ε := by
  set θ : ℝ := min (ε / 8) (1 / 2) with hθ
  set η : ℝ := min (ε / 2) 1 with hη
  have hθ0 : 0 < θ := lt_min (by linarith) (by norm_num)
  have hθ1 : θ ≤ ε / 8 := min_le_left _ _
  have hθ2 : θ ≤ 1 / 2 := min_le_right _ _
  have hη0 : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ ε / 2 := min_le_left _ _
  have hη2 : η ≤ 1 := min_le_right _ _
  obtain ⟨C₁, hC₁, hS⟩ := exists_norm_LFunction_le_mul_rpow_of_half_lt (σ := 1 / 2 + θ)
    (η := η) (by linarith) (by linarith) hη0
  refine ⟨2 * max 8 C₁ * (5 / 4), by positivity, fun N _ χ hχ hGRH t₀ => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  set Q : ℝ := N * (|t₀| + 2) with hQ
  have hQ1 : 1 ≤ Q := by nlinarith [abs_nonneg t₀]
  have hQ0 : 0 < Q := by linarith
  -- comparison of the analytic conductor at height `t` with the one at height `t₀`
  have hcmp : ∀ t : ℝ, (N : ℝ) * (|t| + 2) ≤ Q * (1 + |t - t₀|) := by
    intro t
    have h1 := abs_sub_abs_le_abs_sub t t₀
    have h2 := abs_nonneg (t - t₀)
    have h3 := abs_nonneg t₀
    have h4 : |t| + 2 ≤ (|t₀| + 2) * (1 + |t - t₀|) := by nlinarith
    calc (N : ℝ) * (|t| + 2) ≤ N * ((|t₀| + 2) * (1 + |t - t₀|)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = Q * (1 + |t - t₀|) := by rw [hQ]; ring
  have key := Lindelof.norm_le_mul_rpow_interp_of_vertical_strip (f := LFunction χ)
    (a := 1 / 4) (b := 1 / 2 + θ) (η := η) (Q := Q) (A := 8) (B := C₁) (D := 4 * (N + 1))
    (t₀ := t₀) (z₀ := 1 / 2 + t₀ * I) (by linarith) hη0.le hη2 hQ1 (by norm_num) hC₁
    (fun z _ _ => differentiable_LFunction hχ z)
    (fun z hz _ => by
      have := norm_LFunction_le_four_mul_norm hχ hz
      have h0 : (0 : ℝ) ≤ 4 * (N + 1) := by positivity
      nlinarith [norm_nonneg z])
    (fun z hz => by
      have h0 : 0 ≤ 1 + |z.im - t₀| := by positivity
      calc ‖LFunction χ z‖ ≤ 8 * (N * (|z.im| + 2)) := norm_LFunction_le_of_re_eq_quarter hχ hz
        _ ≤ 8 * (Q * (1 + |z.im - t₀|)) := by linarith [hcmp z.im]
        _ = 8 * Q * (1 + |z.im - t₀|) := by ring)
    (fun z hz => by
      have hzeq : z = ((1 / 2 + θ : ℝ) : ℂ) + z.im * I := by
        apply Complex.ext <;> simp [hz]
      have h0 : 1 ≤ 1 + |z.im - t₀| := by linarith [abs_nonneg (z.im - t₀)]
      have hpos : 0 ≤ (N : ℝ) * (|z.im| + 2) := by positivity
      have hS' := hS N χ hχ hGRH z.im
      rw [← hzeq] at hS'
      calc ‖LFunction χ z‖ ≤ C₁ * ((N : ℝ) * (|z.im| + 2)) ^ η := hS'
        _ ≤ C₁ * (Q * (1 + |z.im - t₀|)) ^ η :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hpos (hcmp z.im) hη0.le) hC₁.le
        _ = C₁ * (Q ^ η * (1 + |z.im - t₀|) ^ η) := by
            rw [Real.mul_rpow hQ0.le (by linarith)]
        _ ≤ C₁ * (Q ^ η * (1 + |z.im - t₀|)) := by
            gcongr
            exact Real.rpow_le_self_of_one_le h0 hη2
        _ = C₁ * Q ^ η * (1 + |z.im - t₀|) := by ring)
    (by simp; norm_num) (by simp; linarith) (by simp)
  have hre : ((1 / 2 : ℂ) + t₀ * I).re = 1 / 2 := by simp
  rw [hre] at key
  have hexp : 1 + (η - 1) / (1 / 2 + θ - 1 / 4) * (1 / 2 - 1 / 4) ≤ ε := by
    have hd : (0 : ℝ) < 1 / 2 + θ - 1 / 4 := by linarith
    rw [div_mul_eq_mul_div, ← le_sub_iff_add_le', div_le_iff₀ hd]
    nlinarith
  have hmax : 0 < max 8 C₁ := lt_max_of_lt_left (by norm_num)
  calc ‖LFunction χ (1 / 2 + t₀ * I)‖
      ≤ 2 * max 8 C₁ * (1 / 2 - 1 / 4 + 1) *
        Q ^ (1 + (η - 1) / (1 / 2 + θ - 1 / 4) * (1 / 2 - 1 / 4)) := key
    _ ≤ 2 * max 8 C₁ * (1 / 2 - 1 / 4 + 1) * Q ^ ε := by
        gcongr
    _ = 2 * max 8 C₁ * (5 / 4) * Q ^ ε := by norm_num

end DirichletCharacter
