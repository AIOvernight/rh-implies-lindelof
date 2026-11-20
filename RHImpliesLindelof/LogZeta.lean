import RHImpliesLindelof.Defs

open Complex Metric

noncomputable section

namespace Lindelof

/-- Uniform bound for the Euler-product logarithm of `ζ` on `Re s ≥ 3/2`. -/
lemma logZeta_euler_bound {s : ℂ} (hs : 3 / 2 ≤ s.re) :
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

/-- Borel–Carathéodory on a disc centred at `c`, on a closed sub-disc. -/
lemma borelCaratheodory_shift {f : ℂ → ℂ} {c : ℂ} {M R r : ℝ} (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball c R)) (hre : ∀ z ∈ ball c R, (f z).re ≤ M)
    (hr : 0 ≤ r) (hrR : r < R) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖f z‖ ≤ 2 * M * r / (R - r) + ‖f c‖ * (R + r) / (R - r) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hmaps : Set.MapsTo (fun w : ℂ ↦ w + c) (ball 0 R) (ball c R) := by
    intro w hw
    simpa [dist_eq_norm] using hw
  have hF : DifferentiableOn ℂ (fun w : ℂ ↦ f (w + c)) (ball 0 R) :=
    hf.comp (by fun_prop) hmaps
  have hx : ‖z - c‖ ≤ r := by simpa [dist_eq_norm] using hz
  have hzc : z - c ∈ ball (0 : ℂ) R := by
    simpa using hx.trans_lt hrR
  have key := Complex.borelCaratheodory (f := fun w : ℂ ↦ f (w + c)) hM hF
    (fun w hw ↦ hre _ (hmaps hw)) hR hzc
  simp only [sub_add_cancel, zero_add] at key
  refine key.trans ?_
  have hd : 0 < R - r := by linarith
  have hx0 : 0 ≤ ‖z - c‖ := norm_nonneg _
  have hfc : 0 ≤ ‖f c‖ := norm_nonneg _
  gcongr

theorem logZetaBound (hRH : RiemannHypothesis) (hG : ZetaPolyGrowth) : LogZetaBound := by
  obtain ⟨A, C₀, hA, hC₀, hgrow⟩ := hG
  intro δ hδ hδ4
  set K : ℝ := 3 / 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) with hKdef
  have hK : 0 ≤ K := by
    have : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
      tsum_nonneg fun p ↦ by positivity
    positivity
  set L : ℝ := |Real.log C₀| with hLdef
  have hL : 0 ≤ L := abs_nonneg _
  refine ⟨6 * (L + 2 * A + 1 + K) / δ + (5 * K + 2), by positivity, fun t ht ↦ ?_⟩
  set c : ℂ := 2 + t * I with hc
  have hlog1 : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_three.le.trans ht
  -- geometry of the ball
  have hgeo : ∀ s ∈ ball c (3 / 2 - δ), |s.re - 2| < 3 / 2 - δ ∧ |s.im - t| < 3 / 2 - δ := by
    intro s hs
    have hs' : ‖s - c‖ < 3 / 2 - δ := by simpa [dist_eq_norm] using hs
    have h1 := abs_re_le_norm (s - c)
    have h2 := abs_im_le_norm (s - c)
    simp only [hc, sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_im, add_im,
      mul_im, re_ofNat, im_ofNat] at h1 h2
    simp only [mul_zero, mul_one, sub_zero, zero_add, add_zero] at h1 h2
    exact ⟨h1.trans_lt hs', h2.trans_lt hs'⟩
  have hne1 : ∀ s ∈ ball c (3 / 2 - δ), s ≠ 1 := by
    intro s hs h
    have := (hgeo s hs).2
    rw [h, abs_lt] at this
    simp at this
    linarith
  have hne0 : ∀ s ∈ ball c (3 / 2 - δ), riemannZeta s ≠ 0 := by
    intro s hs h0
    have hg := hgeo s hs
    rw [abs_lt, abs_lt] at hg
    have him : 0 < s.im := by linarith [hg.2.1]
    have := hRH s h0 (by
      rintro ⟨n, hn⟩
      have := congrArg Complex.im hn
      simp at this
      linarith) (hne1 s hs)
    linarith [hg.1.1]
  have hζd : DifferentiableOn ℂ riemannZeta (ball c (3 / 2 - δ)) := fun s hs ↦
    (differentiableAt_riemannZeta (hne1 s hs)).differentiableWithinAt
  have hfd : DifferentiableOn ℂ (fun s ↦ deriv riemannZeta s / riemannZeta s)
      (ball c (3 / 2 - δ)) :=
    (hζd.deriv isOpen_ball).div hζd hne0
  set g₀ : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-c)) with hg₀
  have hcre : c.re = 2 := by simp [hc]
  have hg₀exp : Complex.exp g₀ = riemannZeta c :=
    riemannZeta_eulerProduct_exp_log (by rw [hcre]; norm_num)
  have hg₀K : ‖g₀‖ ≤ K := logZeta_euler_bound (by rw [hcre]; norm_num)
  obtain ⟨g, hgc, hgd⟩ := hfd.isExactOn_ball.with_val_at c g₀
  have hcB : c ∈ ball c (3 / 2 - δ) := mem_ball_self (by linarith)
  -- ζ * exp (-g) is constant
  have hFd : ∀ s ∈ ball c (3 / 2 - δ),
      HasDerivAt (fun s ↦ riemannZeta s * Complex.exp (-g s)) 0 s := by
    intro s hs
    have h1 := (differentiableAt_riemannZeta (hne1 s hs)).hasDerivAt
    have h2 : HasDerivAt (fun x ↦ Complex.exp (-g x))
        (Complex.exp (-g s) * -(deriv riemannZeta s / riemannZeta s)) s := (hgd s hs).neg.cexp
    have h3 : HasDerivAt (fun x ↦ riemannZeta x * Complex.exp (-g x))
        (deriv riemannZeta s * Complex.exp (-g s) +
          riemannZeta s * (Complex.exp (-g s) * -(deriv riemannZeta s / riemannZeta s))) s :=
      h1.mul h2
    have h0 := hne0 s hs
    refine h3.congr_deriv ?_
    have e : riemannZeta s * (Complex.exp (-g s) * -(deriv riemannZeta s / riemannZeta s))
        = -(deriv riemannZeta s * Complex.exp (-g s)) := by
      field_simp
    rw [e]; ring
  have hexp : ∀ s ∈ ball c (3 / 2 - δ), Complex.exp (g s) = riemannZeta s := by
    intro s hs
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c (3 / 2 - δ)).isPreconnected
      (fun x hx ↦ (hFd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hFd x hx).deriv) hs hcB
    rw [hgc, ← hg₀exp, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero] at hconst
    have : riemannZeta s * Complex.exp (-g s) * Complex.exp (g s) = Complex.exp (g s) := by
      rw [hconst, one_mul]
    rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hgdiff : DifferentiableOn ℂ g (ball c (3 / 2 - δ)) := fun s hs ↦
    (hgd s hs).differentiableAt.differentiableWithinAt
  have hre_le : ∀ s ∈ ball c (3 / 2 - δ), ∀ X : ℝ, ‖riemannZeta s‖ ≤ X → (g s).re ≤ Real.log X := by
    intro s hs X hX
    rw [← hexp s hs, Complex.norm_exp] at hX
    rw [Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hX)]
    exact hX
  refine ⟨g, hgdiff, hexp, ?_, ?_⟩
  · -- outer bound
    intro s hs
    set M : ℝ := L + 2 * A * Real.log t + 1 with hM
    have hMpos : 0 < M := by positivity
    have hsub : ball c (3 / 2 - 3 * δ / 2) ⊆ ball c (3 / 2 - δ) :=
      ball_subset_ball (by linarith)
    have hre : ∀ z ∈ ball c (3 / 2 - 3 * δ / 2), (g z).re ≤ M := by
      intro z hz
      have hzB := hsub hz
      have hg := hgeo z hzB
      rw [abs_lt, abs_lt] at hg
      have him1 : 1 ≤ |z.im| := by
        rw [abs_of_pos (by linarith [hg.2.1])]; linarith [hg.2.1]
      have himt : |z.im| ≤ t ^ 2 := by
        rw [abs_of_pos (by linarith [hg.2.1])]; nlinarith [hg.2.2]
      have hb := hgrow z (by linarith [hg.1.1]) (by linarith [hg.1.2]) him1
      have hb2 : ‖riemannZeta z‖ ≤ C₀ * (t ^ 2) ^ A :=
        hb.trans (by gcongr)
      have h := hre_le z hzB _ hb2
      have ht0 : (0 : ℝ) < t := by linarith
      rw [Real.log_mul hC₀.ne' (by positivity), Real.log_rpow (by positivity),
        Real.log_pow] at h
      have := le_abs_self (Real.log C₀)
      rw [hM, hLdef]
      push_cast at h
      linarith
    have hbc := borelCaratheodory_shift (r := 3 / 2 - 2 * δ) hMpos (hgdiff.mono hsub) hre
      (by linarith) (by linarith) hs
    rw [hgc] at hbc
    have e1 : (3 / 2 - 3 * δ / 2) - (3 / 2 - 2 * δ) = δ / 2 := by ring
    rw [e1] at hbc
    refine hbc.trans ?_
    have hMle : M ≤ (L + 2 * A + 1) * Real.log t := by
      rw [hM]; nlinarith
    have hd2 : 0 < δ / 2 := by positivity
    have s1 : 2 * M * (3 / 2 - 2 * δ) / (δ / 2) ≤ 6 * ((L + 2 * A + 1) * Real.log t) / δ := by
      rw [div_le_div_iff₀ hd2 hδ]
      nlinarith [mul_nonneg hMpos.le hδ.le, mul_le_mul_of_nonneg_right hMle hδ.le]
    have s2 : ‖g₀‖ * (3 / 2 - 3 * δ / 2 + (3 / 2 - 2 * δ)) / (δ / 2) ≤ 6 * (K * Real.log t) / δ := by
      rw [div_le_div_iff₀ hd2 hδ]
      have : K ≤ K * Real.log t := by nlinarith
      have h' : ‖g₀‖ ≤ K * Real.log t := hg₀K.trans this
      nlinarith [mul_nonneg (norm_nonneg g₀) hδ.le, mul_le_mul_of_nonneg_right h' hδ.le,
        norm_nonneg g₀]
    have s3 : 0 ≤ (5 * K + 2) * Real.log t := by positivity
    calc _ ≤ 6 * ((L + 2 * A + 1) * Real.log t) / δ + 6 * (K * Real.log t) / δ := add_le_add s1 s2
      _ ≤ (6 * (L + 2 * A + 1 + K) / δ + (5 * K + 2)) * Real.log t := by
        have : 6 * ((L + 2 * A + 1) * Real.log t) / δ + 6 * (K * Real.log t) / δ
            = 6 * (L + 2 * A + 1 + K) / δ * Real.log t := by ring
        rw [this]; linarith
  · -- inner bound
    intro s hs
    have hsub : ball c (1 / 2) ⊆ ball c (3 / 2 - δ) := ball_subset_ball (by linarith)
    have hre : ∀ z ∈ ball c (1 / 2), (g z).re ≤ K + 1 := by
      intro z hz
      have hzB := hsub hz
      have hz' : ‖z - c‖ < 1 / 2 := by simpa [dist_eq_norm] using hz
      have h1 := abs_re_le_norm (z - c)
      rw [sub_re, hcre, abs_le] at h1
      have hzre : 3 / 2 ≤ z.re := by linarith [h1.1]
      have hb : ‖riemannZeta z‖ ≤ Real.exp K := by
        rw [← riemannZeta_eulerProduct_exp_log (by linarith), Complex.norm_exp]
        exact Real.exp_le_exp.mpr ((re_le_norm _).trans (logZeta_euler_bound hzre))
      have := hre_le z hzB _ hb
      rw [Real.log_exp] at this
      linarith
    have hbc := borelCaratheodory_shift (r := 1 / 4) (by positivity) (hgdiff.mono hsub) hre
      (by norm_num) (by norm_num) hs
    rw [hgc] at hbc
    refine hbc.trans ?_
    have : (0 : ℝ) ≤ 6 * (L + 2 * A + 1 + K) / δ := by positivity
    have e : 2 * (K + 1) * (1 / 4) / (1 / 2 - 1 / 4) + ‖g₀‖ * (1 / 2 + 1 / 4) / (1 / 2 - 1 / 4)
        = 2 * (K + 1) + 3 * ‖g₀‖ := by ring
    rw [e]
    linarith

end Lindelof

#print axioms Lindelof.logZetaBound
