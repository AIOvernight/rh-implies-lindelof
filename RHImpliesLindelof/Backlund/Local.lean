import RHImpliesLindelof.Backlund.ZeroCount

/-!
# A bound for `ζ` to the right of the critical line in terms of the number of nearby zeros

Let `0 < δ ≤ 1 / 8` and `c = 2 + t * I`. We divide `ζ` by the polynomial whose roots are its
zeros in the disc of centre `c` and radius `3 / 2 - 2 * δ`; the quotient `g` is zero-free there,
so it has a holomorphic logarithm, which we bound by the Borel–Carathéodory theorem on a large
disc and on a small disc, and then by Hadamard's three-circles theorem at the point
`1 / 2 + 4 * δ + t * I`. Every bound is explicit in the number `n` of zeros that were removed,
and `n` is at most the number of zeros in four boxes of height one.

## Main results

* `Lindelof.exists_differentiableOn_exp_eq_of_ne_zero`: a holomorphic logarithm of a zero-free
  holomorphic function on a disc.
* `Lindelof.exists_norm_riemannZeta_le_exp_of_zetaZeroCount`: the bound
  `‖ζ(1 / 2 + 4 * δ + t * I)‖ ≤ exp ((C * (1 + n)) ^ (1 - a) * (C * (log t + n)) ^ a + 2 * n)`
  with `n ≤ ∑ j < 4, zetaZeroCount (1 / 2 + δ) (t - 2 + j)`.
-/

open Complex Metric

namespace Lindelof

/-- A zero-free holomorphic function `g` on a disc has a holomorphic logarithm `h` there, which
can be chosen with `h c = log (g c)` at the centre. -/
theorem exists_differentiableOn_exp_eq_of_ne_zero {g : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (ball c ρ)) (hne : ∀ z ∈ ball c ρ, g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c ρ) ∧ (∀ z ∈ ball c ρ, exp (h z) = g z) ∧
      h c = Complex.log (g c) := by
  have hcB : c ∈ ball c ρ := mem_ball_self hρ
  have hfd : DifferentiableOn ℂ (fun s ↦ deriv g s / g s) (ball c ρ) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨h, hhc, hhd⟩ := hfd.isExactOn_ball.with_val_at c (Complex.log (g c))
  have hFd : ∀ s ∈ ball c ρ, HasDerivAt (fun s ↦ g s * Complex.exp (-h s)) 0 s := by
    intro s hs
    have h1 := (hg.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt
    have h2 : HasDerivAt (fun x ↦ Complex.exp (-h x))
        (Complex.exp (-h s) * -(deriv g s / g s)) s := (hhd s hs).neg.cexp
    have h3 := h1.mul h2
    have h0 := hne s hs
    refine h3.congr_deriv ?_
    have e : g s * (Complex.exp (-h s) * -(deriv g s / g s))
        = -(deriv g s * Complex.exp (-h s)) := by
      field_simp
    rw [e]; ring
  refine ⟨h, fun s hs ↦ (hhd s hs).differentiableAt.differentiableWithinAt, fun s hs ↦ ?_, hhc⟩
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c ρ).isPreconnected
    (fun x hx ↦ (hFd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hFd x hx).deriv) hs hcB
  have hc1 : g c * Complex.exp (-h c) = 1 := by
    rw [hhc, Complex.exp_neg, Complex.exp_log (hne c hcB), mul_inv_cancel₀ (hne c hcB)]
  rw [hc1] at hconst
  have : g s * Complex.exp (-h s) * Complex.exp (h s) = Complex.exp (h s) := by
    rw [hconst, one_mul]
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- **A bound for `ζ` in terms of the number of nearby zeros.** For `0 < δ ≤ 1 / 8` there are
`C > 0`, `0 < a < 1` and `t₀` such that for every `t ≥ t₀` there is a natural number `n`, at
most the number of zeros `ρ` of `ζ` with `1 / 2 + δ < re ρ` and `t - 2 < im ρ ≤ t + 2` counted
with multiplicity, such that
`‖ζ(1 / 2 + 4 * δ + t * I)‖ ≤ exp ((C * (1 + n)) ^ (1 - a) * (C * (log t + n)) ^ a + 2 * n)`. -/
theorem exists_norm_riemannZeta_le_exp_of_zetaZeroCount {δ : ℝ} (hδ : 0 < δ)
    (hδ8 : δ ≤ 1 / 8) :
    ∃ C a t₀ : ℝ, 0 < C ∧ 0 < a ∧ a < 1 ∧ ∀ t : ℝ, t₀ ≤ t → ∃ n : ℕ,
      n ≤ ∑ j ∈ Finset.range 4, zetaZeroCount (1 / 2 + δ) (t - 2 + j) ∧
      ‖riemannZeta (((1 / 2 + 4 * δ : ℝ) : ℂ) + t * I)‖ ≤
        Real.exp ((C * (1 + n)) ^ (1 - a) * (C * (Real.log t + n)) ^ a + 2 * n) := by
  obtain ⟨K, hK, hζ⟩ := exists_exp_neg_le_norm_riemannZeta
  obtain ⟨T₀, hfinite⟩ := exists_finite_zetaZeroBox (σ := 1 / 2 + δ) (by linarith)
  set D : ℝ := Real.log (2 / δ) with hD
  have hD0 : 0 < D := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  set C : ℝ := 5 * K + 14 + (3 * D + 3 * K + 33) / δ with hC
  have hC3 : (3 * D + 3 * K + 33) / δ ≤ C := by rw [hC]; linarith
  have hC1 : 5 * K + 14 ≤ C := by
    have : 0 ≤ (3 * D + 3 * K + 33) / δ := by positivity
    rw [hC]; linarith
  have hC0 : 0 < C := by linarith
  set a : ℝ := Real.log ((3 / 2 - 4 * δ) / (1 / 4)) / Real.log ((3 / 2 - 3 * δ) / (1 / 4))
    with ha
  have hnum : 0 < Real.log ((3 / 2 - 4 * δ) / (1 / 4)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have hlt : Real.log ((3 / 2 - 4 * δ) / (1 / 4)) < Real.log ((3 / 2 - 3 * δ) / (1 / 4)) := by
    apply Real.log_lt_log
    · apply div_pos <;> linarith
    · exact div_lt_div_of_pos_right (by linarith) (by norm_num)
  have ha0 : 0 < a := div_pos hnum (hnum.trans hlt)
  have ha1 : a < 1 := (div_lt_one (hnum.trans hlt)).2 hlt
  refine ⟨C, a, max 3 (T₀ + 2), hC0, ha0, ha1, fun t ht ↦ ?_⟩
  have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
  have htT : T₀ + 2 ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := by linarith
  set L : ℝ := Real.log t with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le ht0]
    exact Real.exp_one_lt_three.le.trans ht3
  set c : ℂ := 2 + t * I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcim : c.im = t := by simp [hc]
  have hgeo : ∀ {ρ : ℝ} {w : ℂ}, dist w c ≤ ρ → |w.re - 2| ≤ ρ ∧ |w.im - t| ≤ ρ := by
    intro ρ w hw
    rw [dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - c)
    have h2 := abs_im_le_norm (w - c)
    rw [sub_re, hcre] at h1
    rw [sub_im, hcim] at h2
    exact ⟨h1.trans hw, h2.trans hw⟩
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c (3 / 2)) := by
    intro w hw
    have hg := (hgeo (mem_ball.1 hw).le).2
    rw [abs_le] at hg
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    rintro rfl
    simp at hg
    linarith [hg.1]
  set B : ℝ := 25 * (t + 2) with hB
  have hBc : ∀ w ∈ closedBall c (3 / 2 - δ), ‖riemannZeta w‖ ≤ B := by
    intro w hw
    obtain ⟨h1, h2⟩ := hgeo (mem_closedBall.1 hw)
    rw [abs_le] at h1 h2
    have h0 : 0 ≤ w.im := by linarith [h2.1]
    have := norm_riemannZeta_le_mul_abs_im (s := w) (by linarith [h1.1]) (by linarith [h1.2])
      (by rw [abs_of_nonneg h0]; linarith [h2.1])
    rw [abs_of_nonneg h0] at this
    rw [hB]
    linarith [h2.2]
  have hcζ := hζ c (by rw [hcre]; norm_num)
  have hcpos : 0 < ‖riemannZeta c‖ := (Real.exp_pos _).trans_le hcζ.1
  have h2r : 3 / 2 - 2 * δ < 3 / 2 - δ := by linarith
  obtain ⟨Z, g, hfact, -⟩ := exists_isZeroFactorization (r₂ := 3 / 2 - 2 * δ)
    (r := 3 / 2 - δ) (R := 3 / 2) (by linarith) h2r (by linarith) hdiff hBc
    (norm_pos_iff.1 hcpos)
  set n : ℕ := Z.card with hn
  have hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 1 / 2 + 2 * δ ≤ ρ.re ∧ ρ.re < 1 ∧
      |ρ.im - t| ≤ 3 / 2 - 2 * δ ∧ ‖ρ - c‖ ≤ 3 / 2 - 2 * δ := by
    intro ρ hρ
    have h0 := hfact.eq_zero_of_mem h2r hρ
    have hmem := hfact.mem_closedBall ρ hρ
    obtain ⟨h1, h2⟩ := hgeo (mem_closedBall.1 hmem)
    rw [abs_le] at h1
    refine ⟨h0, by linarith [h1.1], ?_, h2, by simpa [dist_eq_norm] using hmem⟩
    by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hcon) h0
  refine ⟨n, ?_, ?_⟩
  · -- the zeros that were removed lie in four boxes of height one
    refine hfact.card_le_sum_finsum_toNat_analyticOrderAt h2r (Finset.range 4)
      (fun j : ℕ ↦ zetaZeroBox (1 / 2 + δ) (t - 2 + j))
      (fun j ↦ hfinite _ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])) ?_
    intro ρ hρ
    obtain ⟨h0, hre, -, him, -⟩ := hZ ρ hρ
    rw [abs_le] at him
    have key : ∀ j : ℕ, t - 2 + j < ρ.im → ρ.im ≤ t - 2 + j + 1 →
        ρ ∈ zetaZeroBox (1 / 2 + δ) (t - 2 + j) := fun j h1 h2 ↦ ⟨h0, by linarith, h1, h2⟩
    rcases le_or_gt ρ.im (t - 1) with h1 | h1
    · exact ⟨0, by simp, key 0 (by push_cast; linarith [him.1]) (by push_cast; linarith)⟩
    rcases le_or_gt ρ.im t with h2 | h2
    · exact ⟨1, by simp, key 1 (by push_cast; linarith) (by push_cast; linarith)⟩
    rcases le_or_gt ρ.im (t + 1) with h3 | h3
    · exact ⟨2, by simp, key 2 (by push_cast; linarith) (by push_cast; linarith)⟩
    · exact ⟨3, by simp, key 3 (by push_cast; linarith) (by push_cast; linarith [him.2])⟩
  · set P : ℂ → ℂ := fun z ↦ (Z.map fun ρ ↦ z - ρ).prod with hP
    have hfac : ∀ z ∈ ball c (3 / 2 - δ), riemannZeta z = P z * g z := hfact.eq_prod_mul
    -- the cofactor `g` is bounded on the disc of radius `3 / 2 - 3 * δ / 2`
    have hg1 : ∀ z ∈ closedBall c (3 / 2 - 3 * δ / 2), ‖g z‖ ≤ B * (2 / δ) ^ n := by
      intro z hz
      have hr' : (0 : ℝ) < 3 / 2 - 3 * δ / 2 := by linarith
      have hcl : closure (ball c (3 / 2 - 3 * δ / 2)) = closedBall c (3 / 2 - 3 * δ / 2) :=
        closure_ball c hr'.ne'
      refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (hfact.differentiableOn.diffContOnCl_ball (closedBall_subset_ball (by linarith))) ?_
        (hcl ▸ hz)
      intro v hv
      rw [frontier_ball c hr'.ne', mem_sphere, dist_eq_norm] at hv
      have hvb : v ∈ ball c (3 / 2 - δ) := by
        rw [mem_ball, dist_eq_norm, hv]; linarith
      have hlow : (δ / 2) ^ n ≤ ‖P v‖ :=
        pow_card_le_norm_multiset_prod_sub Z (by positivity) fun ρ hρ ↦ by
          have h5 := (hZ ρ hρ).2.2.2.2
          have := norm_sub_norm_le (v - c) (ρ - c)
          rw [sub_sub_sub_cancel_right] at this
          linarith
      have hζv := hBc v (by rw [mem_closedBall, dist_eq_norm, hv]; linarith)
      rw [hfac v hvb, norm_mul] at hζv
      have hpos : 0 < (δ / 2) ^ n := by positivity
      have h1 : (δ / 2) ^ n * ‖g v‖ ≤ B :=
        (mul_le_mul_of_nonneg_right hlow (norm_nonneg _)).trans hζv
      have e : B * (2 / δ) ^ n = B / (δ / 2) ^ n := by
        have e2 : 2 / δ = (δ / 2)⁻¹ := by rw [inv_div]
        rw [e2, inv_pow]
        exact (div_eq_mul_inv _ _).symm
      rw [e, le_div_iff₀ hpos]
      linarith
    -- a logarithm of `g`
    have hgne : ∀ z ∈ ball c (3 / 2 - 2 * δ), g z ≠ 0 := fun z hz ↦
      hfact.ne_zero z (ball_subset_closedBall hz)
    obtain ⟨h, hhd, hhexp, hhc⟩ := exists_differentiableOn_exp_eq_of_ne_zero (c := c)
      (by linarith : (0 : ℝ) < 3 / 2 - 2 * δ)
      (hfact.differentiableOn.mono (ball_subset_ball h2r.le)) hgne
    have hre_le : ∀ z ∈ ball c (3 / 2 - 2 * δ), ∀ X : ℝ, ‖g z‖ ≤ Real.exp X →
        (h z).re ≤ X := by
      intro z hz X hX
      rw [← hhexp z hz, Complex.norm_exp, Real.exp_le_exp] at hX
      exact hX
    -- the value at the centre
    have hPc1 : 1 ≤ ‖P c‖ := by
      have := pow_card_le_norm_multiset_prod_sub Z (z := c) zero_le_one fun ρ hρ ↦ by
        have h3 := (hZ ρ hρ).2.2.1
        have := re_le_norm (c - ρ)
        rw [sub_re, hcre] at this
        linarith
      simpa using this
    have hPc2 : ‖P c‖ ≤ Real.exp n := by
      have := norm_multiset_prod_sub_le Z (z := c) (D := Real.exp 1) fun ρ hρ ↦ by
        have h5 := (hZ ρ hρ).2.2.2.2
        rw [norm_sub_rev]
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      rwa [← Real.exp_nat_mul, mul_one] at this
    have hPcpos : 0 < ‖P c‖ := by linarith
    have hgc : ‖g c‖ = ‖riemannZeta c‖ / ‖P c‖ := by
      rw [hfac c (mem_ball_self (by linarith)), norm_mul, mul_div_cancel_left₀ _ hPcpos.ne']
    have hhc_le : ‖h c‖ ≤ K + n + 4 := by
      rw [hhc]
      have h1 := norm_le_abs_re_add_abs_im (Complex.log (g c))
      rw [Complex.log_re, Complex.log_im] at h1
      have h2 := Complex.abs_arg_le_pi (g c)
      have h3 := Real.pi_le_four
      have h4 : |Real.log ‖g c‖| ≤ K + n := by
        rw [hgc, Real.log_div hcpos.ne' hPcpos.ne']
        have hl1 : -K ≤ Real.log ‖riemannZeta c‖ := by
          rw [Real.le_log_iff_exp_le hcpos]; exact hcζ.1
        have hl2 : Real.log ‖riemannZeta c‖ ≤ K := by
          rw [Real.log_le_iff_le_exp hcpos]; exact hcζ.2
        have hl3 : 0 ≤ Real.log ‖P c‖ := Real.log_nonneg hPc1
        have hl4 : Real.log ‖P c‖ ≤ n := by
          rw [Real.log_le_iff_le_exp hPcpos]; exact hPc2
        rw [abs_le]
        constructor <;> linarith
      linarith
    -- the bound on the large disc
    have ht5 : B ≤ Real.exp (5 * L) := by
      have e : Real.exp (5 * L) = t ^ 5 := by
        rw [show (5 : ℝ) * L = (5 : ℕ) * L by norm_num, Real.exp_nat_mul, hL, Real.exp_log ht0]
      have h4 : (3 : ℝ) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by norm_num) ht3 4
      have e' : t ^ 5 = t * t ^ 4 := by ring
      norm_num at h4
      have h5 := mul_le_mul_of_nonneg_left h4 ht0.le
      rw [e, e', hB]
      linarith
    have hδpow : (2 / δ) ^ n = Real.exp (n * D) := by
      rw [Real.exp_nat_mul, hD, Real.exp_log (by positivity)]
    have houter : ∀ z ∈ closedBall c (3 / 2 - 3 * δ), ‖h z‖ ≤ C * (L + n) := by
      intro z hz
      set M : ℝ := 5 * L + n * D + 1 with hM
      have hMpos : 0 < M := by positivity
      have hre : ∀ w ∈ ball c (3 / 2 - 2 * δ), (h w).re ≤ M := by
        intro w hw
        have := hre_le w hw (5 * L + n * D) (by
          rw [Real.exp_add, ← hδpow]
          exact (hg1 w (closedBall_subset_closedBall (by linarith)
            (ball_subset_closedBall hw))).trans (by gcongr))
        linarith
      have hbc := borelCaratheodory_closedBall (r := 3 / 2 - 3 * δ) hMpos hhd hre
        (by linarith) (by linarith) hz
      have e1 : (3 / 2 - 2 * δ) - (3 / 2 - 3 * δ) = δ := by ring
      rw [e1, ← add_div] at hbc
      refine hbc.trans ?_
      rw [div_le_iff₀ hδ]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have s1 : 2 * M * (3 / 2 - 3 * δ) ≤ 3 * M := by
        have : 0 ≤ M * δ := by positivity
        linarith
      have s2 : ‖h c‖ * (3 / 2 - 2 * δ + (3 / 2 - 3 * δ)) ≤ 3 * (K + n + 4) := by
        have : 0 ≤ ‖h c‖ * δ := by positivity
        linarith
      have s3 : 3 * M + 3 * (K + n + 4) ≤ (3 * D + 3 * K + 33) * (L + n) := by
        have e3 : (3 * D + 3 * K + 33) * (L + n) - (3 * M + 3 * (K + n + 4)) =
            3 * (D * L) + 3 * (K * (L - 1)) + 18 * (L - 1) + 3 + 3 * (K * n) + 30 * n := by
          rw [hM]; ring
        have p1 : 0 ≤ D * L := mul_nonneg hD0.le (zero_le_one.trans hL1)
        have p2 : 0 ≤ K * (L - 1) := mul_nonneg hK (sub_nonneg.2 hL1)
        have p3 : 0 ≤ K * n := mul_nonneg hK hn0
        linarith
      have s4 : 3 * D + 3 * K + 33 ≤ C * δ := (div_le_iff₀ hδ).1 hC3
      have s5 : (3 * D + 3 * K + 33) * (L + n) ≤ C * δ * (L + n) :=
        mul_le_mul_of_nonneg_right s4 (by linarith)
      linarith
    -- the bound on the small disc
    have hinner : ∀ z ∈ closedBall c (1 / 4), ‖h z‖ ≤ C * (1 + n) := by
      intro z hz
      have hsub : ball c (1 / 2) ⊆ ball c (3 / 2 - 2 * δ) := ball_subset_ball (by linarith)
      have hre : ∀ w ∈ ball c (1 / 2), (h w).re ≤ K + n + 1 := by
        intro w hw
        have hwre : 3 / 2 ≤ w.re := by
          have := (hgeo (mem_ball.1 hw).le).1
          rw [abs_le] at this
          linarith [this.1]
        have hwb : w ∈ ball c (3 / 2 - δ) := ball_subset_ball (by linarith) hw
        have hlow : (1 / 2 : ℝ) ^ n ≤ ‖P w‖ :=
          pow_card_le_norm_multiset_prod_sub Z (by norm_num) fun ρ hρ ↦ by
            have h3 := (hZ ρ hρ).2.2.1
            have := re_le_norm (w - ρ)
            rw [sub_re] at this
            linarith
        have hζw := (hζ w hwre).2
        rw [hfac w hwb, norm_mul] at hζw
        have hgw : ‖g w‖ ≤ Real.exp (K + n) := by
          have hpos : (0 : ℝ) < (1 / 2) ^ n := by positivity
          have h1 : (1 / 2 : ℝ) ^ n * ‖g w‖ ≤ Real.exp K :=
            (mul_le_mul_of_nonneg_right hlow (norm_nonneg _)).trans hζw
          have h2 : (2 : ℝ) ^ n ≤ Real.exp n := by
            have := pow_le_pow_left₀ (by norm_num) (Real.add_one_le_exp (1 : ℝ)) n
            rw [← Real.exp_nat_mul, mul_one] at this
            norm_num at this
            exact this
          have h3 : ‖g w‖ ≤ Real.exp K * 2 ^ n := by
            have e : Real.exp K * 2 ^ n = Real.exp K / (1 / 2) ^ n := by
              rw [div_eq_mul_inv, ← inv_pow]; norm_num
            rw [e, le_div_iff₀ hpos]
            linarith
          rw [Real.exp_add]
          exact h3.trans (by gcongr)
        linarith [hre_le w (hsub hw) _ hgw]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hbc := borelCaratheodory_closedBall (r := 1 / 4) (by positivity) (hhd.mono hsub) hre
        (by norm_num) (by norm_num) hz
      refine hbc.trans ?_
      have e : 2 * (K + n + 1) * (1 / 4) / (1 / 2 - 1 / 4) +
          ‖h c‖ * (1 / 2 + 1 / 4) / (1 / 2 - 1 / 4) = 2 * (K + n + 1) + 3 * ‖h c‖ := by ring
      rw [e]
      have h5 : (5 * K + 14) * (1 + n) ≤ C * (1 + n) :=
        mul_le_mul_of_nonneg_right hC1 (by linarith)
      have p3 : 0 ≤ K * n := mul_nonneg hK hn0
      linarith
    -- three circles
    set z₀ : ℂ := ((1 / 2 + 4 * δ : ℝ) : ℂ) + t * I with hz₀
    have hdist : dist z₀ c = 3 / 2 - 4 * δ := by
      rw [Complex.dist_eq]
      have : z₀ - c = ((1 / 2 + 4 * δ - 2 : ℝ) : ℂ) := by
        rw [hz₀, hc]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have hb := norm_le_interp_of_mem_sphere (M₁ := C * (1 + n)) (M₃ := C * (L + n))
      (by norm_num : (0 : ℝ) < 1 / 4) (by linarith : (1 / 4 : ℝ) < 3 / 2 - 4 * δ)
      (by linarith : 3 / 2 - 4 * δ < 3 / 2 - 3 * δ)
      (by linarith : 3 / 2 - 3 * δ < 3 / 2 - 2 * δ) hhd
      (fun z hz ↦ hinner z (sphere_subset_closedBall hz))
      (fun z hz ↦ houter z (sphere_subset_closedBall hz)) (mem_sphere.2 hdist)
    rw [← ha] at hb
    have hz₀b : z₀ ∈ ball c (3 / 2 - 2 * δ) := by
      rw [mem_ball, hdist]; linarith
    have hPz : ‖P z₀‖ ≤ Real.exp (2 * n) := by
      have := norm_multiset_prod_sub_le Z (z := z₀) (D := Real.exp 2) fun ρ hρ ↦ by
        have h5 := (hZ ρ hρ).2.2.2.2
        have h6 : ‖z₀ - c‖ = 3 / 2 - 4 * δ := by rw [← dist_eq_norm]; exact hdist
        have h7 := norm_sub_le (z₀ - c) (ρ - c)
        rw [sub_sub_sub_cancel_right] at h7
        have := Real.add_one_le_exp (2 : ℝ)
        linarith
      rwa [← Real.exp_nat_mul, mul_comm] at this
    rw [hfac z₀ (ball_subset_ball h2r.le hz₀b), norm_mul, ← hhexp z₀ hz₀b, Complex.norm_exp]
    calc ‖P z₀‖ * Real.exp (h z₀).re
        ≤ Real.exp (2 * n) * Real.exp ((C * (1 + n)) ^ (1 - a) * (C * (L + n)) ^ a) := by
          gcongr
          exact (re_le_norm _).trans hb
      _ = Real.exp ((C * (1 + n)) ^ (1 - a) * (C * (L + n)) ^ a + 2 * n) := by
          rw [← Real.exp_add, add_comm]

end Lindelof
