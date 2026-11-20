import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import RHImpliesLindelof.BorelCaratheodory

/-!
# A one-sided bound for the logarithmic derivative of a holomorphic function

Let `f` be holomorphic near the closed disc of centre `c` and radius `r`, bounded by `B` there,
with `f c ≠ 0`. This file proves a lower bound for the real part of `f' / f` at points lying to
the right of all zeros of `f` (a one-sided form of Landau's lemma
`f' / f = ∑ 1 / (z - ρ) + O(log (B / ‖f c‖))`).

The proof removes the zeros of `f` in a smaller disc one at a time by dividing by Blaschke
factors of the big disc: each division multiplies `‖f c‖` by at least `r / r₂ > 1` without
increasing the supremum, so the process stops after at most `log (B / ‖f c‖) / log (r / r₂)`
steps, and each step changes `re (f' / f)` by a positive term plus a bounded one. Once no zero
is left, the Borel–Carathéodory theorem applied to a logarithm of `f` and a Cauchy estimate
bound `f' / f`.

## Main results

* `Complex.norm_deriv_div_le_of_forall_mem_ball_ne_zero`: if `f` is holomorphic, zero-free and
  bounded by `B` on `ball c r₂`, then `‖f' / f‖ ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * log (B / ‖f c‖)` on
  `closedBall c r₁`.
* `Complex.exists_neg_mul_log_le_re_deriv_div`: for `0 < r₁ < r₂ < r < R` there is `K ≥ 0` such
  that, if `f` is holomorphic on `ball c R`, bounded by `B` on `closedBall c r`, `f c ≠ 0` and
  all zeros of `f` in `closedBall c r₂` have real part `≤ a`, then
  `-(K * log (B / ‖f c‖)) ≤ re (f' z / f z)` for `z ∈ closedBall c r₁` with `a < re z`.
-/

open Metric Set

namespace Complex

/-- If `f` is holomorphic and zero-free on `ball c r₂` and bounded by `B` there, then on the
smaller closed disc `closedBall c r₁` its logarithmic derivative is bounded by
`8 * r₂ / (r₂ - r₁) ^ 2 * log (B / ‖f c‖)`. -/
theorem norm_deriv_div_le_of_forall_mem_ball_ne_zero {f : ℂ → ℂ} {c : ℂ} {r₁ r₂ B : ℝ}
    (hr₁ : 0 < r₁) (h12 : r₁ < r₂) (hf : DifferentiableOn ℂ f (ball c r₂))
    (hne : ∀ z ∈ ball c r₂, f z ≠ 0) (hB : ∀ z ∈ ball c r₂, ‖f z‖ ≤ B) {z : ℂ}
    (hz : z ∈ closedBall c r₁) :
    ‖deriv f z / f z‖ ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * Real.log (B / ‖f c‖) := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hcB : c ∈ ball c r₂ := mem_ball_self hr₂
  have hfc : 0 < ‖f c‖ := norm_pos_iff.2 (hne c hcB)
  have hBpos : 0 < B := hfc.trans_le (hB c hcB)
  have hE : 0 ≤ Real.log (B / ‖f c‖) :=
    Real.log_nonneg ((one_le_div hfc).2 (hB c hcB))
  set d : ℝ := (r₂ - r₁) / 2 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hfd : DifferentiableOn ℂ (fun s ↦ deriv f s / f s) (ball c r₂) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨g, hgc, hgd⟩ := hfd.isExactOn_ball.with_val_at c (Complex.log (f c))
  -- `f * exp (-g)` is constant
  have hFd : ∀ s ∈ ball c r₂, HasDerivAt (fun s ↦ f s * Complex.exp (-g s)) 0 s := by
    intro s hs
    have h1 := (hf.differentiableAt (isOpen_ball.mem_nhds hs)).hasDerivAt
    have h2 : HasDerivAt (fun x ↦ Complex.exp (-g x))
        (Complex.exp (-g s) * -(deriv f s / f s)) s := (hgd s hs).neg.cexp
    have h3 := h1.mul h2
    have h0 := hne s hs
    refine h3.congr_deriv ?_
    have e : f s * (Complex.exp (-g s) * -(deriv f s / f s))
        = -(deriv f s * Complex.exp (-g s)) := by
      field_simp
    rw [e]; ring
  have hexp : ∀ s ∈ ball c r₂, Complex.exp (g s) = f s := by
    intro s hs
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r₂).isPreconnected
      (fun x hx ↦ (hFd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (hFd x hx).deriv) hs hcB
    have hc1 : f c * Complex.exp (-g c) = 1 := by
      rw [hgc, Complex.exp_neg, Complex.exp_log (hne c hcB), mul_inv_cancel₀ (hne c hcB)]
    rw [hc1] at hconst
    have : f s * Complex.exp (-g s) * Complex.exp (g s) = Complex.exp (g s) := by
      rw [hconst, one_mul]
    rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hgre : ∀ s ∈ ball c r₂, (g s).re = Real.log ‖f s‖ := by
    intro s hs
    rw [← hexp s hs, Complex.norm_exp, Real.log_exp]
  have hgdiff : DifferentiableOn ℂ g (ball c r₂) := fun s hs ↦
    (hgd s hs).differentiableAt.differentiableWithinAt
  set h : ℂ → ℂ := fun s ↦ g s - g c with hh
  have hhdiff : DifferentiableOn ℂ h (ball c r₂) := hgdiff.sub_const _
  have hhc : h c = 0 := by simp [hh]
  have hzc : dist z c ≤ r₁ := mem_closedBall.1 hz
  have hzB : z ∈ ball c r₂ := mem_ball.2 (hzc.trans_lt h12)
  have hderiv : deriv h z = deriv f z / f z := ((hgd z hzB).sub_const (g c)).deriv
  have hsub : closedBall z d ⊆ closedBall c (r₁ + d) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w z c]
  have hsub' : closedBall c (r₁ + d) ⊆ ball c r₂ := closedBall_subset_ball (by rw [hd]; linarith)
  -- bound for every `M` larger than `log (B / ‖f c‖)`
  have key : ∀ M : ℝ, Real.log (B / ‖f c‖) < M →
      ‖deriv f z / f z‖ ≤ 8 * r₂ / (r₂ - r₁) ^ 2 * M := by
    intro M hM
    have hMpos : 0 < M := hE.trans_lt hM
    have hre : ∀ s ∈ ball c r₂, (h s).re ≤ M := by
      intro s hs
      have hfs : 0 < ‖f s‖ := norm_pos_iff.2 (hne s hs)
      simp only [hh, sub_re]
      rw [hgre s hs, hgre c hcB, ← Real.log_div hfs.ne' hfc.ne']
      refine (Real.log_le_log (div_pos hfs hfc) ?_).trans hM.le
      gcongr
      exact hB s hs
    have hbc : ∀ w ∈ closedBall c (r₁ + d), ‖h w‖ ≤ 2 * M * (r₁ + d) / d := by
      intro w hw
      have := Lindelof.borelCaratheodory_closedBall hMpos hhdiff hre
        (by positivity : (0 : ℝ) ≤ r₁ + d) (by rw [hd]; linarith) hw
      rw [hhc, norm_zero, zero_mul, zero_div, add_zero] at this
      have e : r₂ - (r₁ + d) = d := by rw [hd]; ring
      rwa [e] at this
    have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hd0
      (hhdiff.diffContOnCl_ball (hsub.trans hsub'))
      (fun w hw ↦ hbc w (hsub (sphere_subset_closedBall hw)))
    rw [hderiv] at hcauchy
    refine hcauchy.trans ?_
    have e : 2 * M * (r₁ + d) / d / d = 8 * (r₁ + d) / (r₂ - r₁) ^ 2 * M := by
      rw [hd]; field_simp; ring
    rw [e]
    have : 0 < (r₂ - r₁) ^ 2 := by nlinarith
    gcongr
    rw [hd]; linarith
  have hK : 0 < 8 * r₂ / (r₂ - r₁) ^ 2 := by
    have : 0 < (r₂ - r₁) ^ 2 := by nlinarith
    positivity
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have := key (Real.log (B / ‖f c‖) + ε / (8 * r₂ / (r₂ - r₁) ^ 2))
    (lt_add_of_pos_right _ (div_pos hε hK))
  rwa [mul_add, mul_div_cancel₀ _ hK.ne'] at this

/-- **One-sided Landau lemma**. For `0 < r₁ < r₂ < r < R` there is a constant `K ≥ 0` such
that: if `f` is holomorphic on `ball c R`, bounded by `B` on `closedBall c r`, `f c ≠ 0`, and
every zero of `f` in `closedBall c r₂` has real part at most `a`, then
`-(K * log (B / ‖f c‖)) ≤ re (f' z / f z)` for every `z ∈ closedBall c r₁` with `a < re z`. -/
theorem exists_neg_mul_log_le_re_deriv_div {r₁ r₂ r R : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ < r₂)
    (h2r : r₂ < r) (hrR : r < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℂ → ℂ) (c : ℂ) (a B : ℝ),
      DifferentiableOn ℂ f (ball c R) → (∀ z ∈ closedBall c r, ‖f z‖ ≤ B) → f c ≠ 0 →
      (∀ ρ ∈ closedBall c r₂, f ρ = 0 → ρ.re ≤ a) →
      ∀ z ∈ closedBall c r₁, a < z.re → -(K * Real.log (B / ‖f c‖)) ≤ (deriv f z / f z).re := by
  have hr₂ : 0 < r₂ := hr₁.trans h12
  have hr : 0 < r := hr₂.trans h2r
  set lam : ℝ := Real.log (r / r₂) with hlam
  have hlam0 : 0 < lam := Real.log_pos ((one_lt_div hr₂).2 h2r)
  set K₀ : ℝ := 8 * r₂ / (r₂ - r₁) ^ 2 with hK₀
  have hK₀pos : 0 ≤ K₀ := by
    have : 0 < (r₂ - r₁) ^ 2 := by nlinarith
    positivity
  set K₁ : ℝ := r₂ / (r * (r - r₂)) with hK₁
  have hrr : 0 < r * (r - r₂) := mul_pos hr (by linarith)
  have hK₁pos : 0 ≤ K₁ := by positivity
  set K : ℝ := K₀ + K₁ / lam with hKdef
  have hK : 0 ≤ K := by positivity
  have hKlam : K₁ ≤ K * lam := by
    rw [hKdef, add_mul, div_mul_cancel₀ _ hlam0.ne']
    nlinarith
  refine ⟨K, hK, fun f c a B hf hB hfc hzero z hz haz ↦ ?_⟩
  -- induction on the number of zeros that may have to be removed
  have main : ∀ n : ℕ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball c R) →
      (∀ z ∈ closedBall c r, ‖f z‖ ≤ B) → f c ≠ 0 →
      (∀ ρ ∈ closedBall c r₂, f ρ = 0 → ρ.re ≤ a) → Real.log (B / ‖f c‖) < n * lam →
      -(K * Real.log (B / ‖f c‖)) ≤ (deriv f z / f z).re := by
    intro n
    induction n with
    | zero =>
      intro f _ hB hfc _ hn
      have hfc' : 0 < ‖f c‖ := norm_pos_iff.2 hfc
      have : 0 ≤ Real.log (B / ‖f c‖) :=
        Real.log_nonneg ((one_le_div hfc').2 (hB c (mem_closedBall_self hr.le)))
      simp only [Nat.cast_zero, zero_mul] at hn
      linarith
    | succ n ih =>
      intro f hf hB hfc hzero hn
      have hfc' : 0 < ‖f c‖ := norm_pos_iff.2 hfc
      have hE : 0 ≤ Real.log (B / ‖f c‖) :=
        Real.log_nonneg ((one_le_div hfc').2 (hB c (mem_closedBall_self hr.le)))
      by_cases hex : ∃ ρ ∈ closedBall c r₂, f ρ = 0
      · obtain ⟨ρ, hρ, hfρ⟩ := hex
        have hρa : ρ.re ≤ a := hzero ρ hρ hfρ
        have hρc : ‖ρ - c‖ ≤ r₂ := by simpa [dist_eq_norm] using hρ
        have hcρ : c - ρ ≠ 0 := by
          intro h0
          rw [sub_eq_zero] at h0
          exact hfc (h0 ▸ hfρ)
        have hcρn : 0 < ‖c - ρ‖ := norm_pos_iff.2 hcρ
        have hcρle : ‖c - ρ‖ ≤ r₂ := by rwa [norm_sub_rev]
        have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
        set D : ℂ → ℂ := fun w ↦ (r : ℂ) ^ 2 - (starRingEnd ℂ) (ρ - c) * (w - c) with hD
        set f₁ : ℂ → ℂ := fun w ↦ dslope f ρ w * D w / r with hf₁
        have hfac : ∀ w, f w * D w = r * (w - ρ) * f₁ w := by
          intro w
          have h1 := sub_smul_dslope f ρ w
          rw [hfρ, sub_zero, smul_eq_mul] at h1
          simp only [hf₁]
          rw [← h1]
          field_simp
        have hρR : ball c R ∈ nhds ρ :=
          isOpen_ball.mem_nhds (mem_ball.2 ((mem_closedBall.1 hρ).trans_lt (h2r.trans hrR)))
        have hDdiff : Differentiable ℂ D := by
          simp only [hD]; fun_prop
        have hf₁diff : DifferentiableOn ℂ f₁ (ball c R) :=
          (((differentiableOn_dslope hρR).2 hf).mul hDdiff.differentiableOn).div_const _
        have hDlow : ∀ w, r ^ 2 - r₂ * ‖w - c‖ ≤ ‖D w‖ := by
          intro w
          have h1 : ‖(r : ℂ) ^ 2‖ - ‖(starRingEnd ℂ) (ρ - c) * (w - c)‖ ≤ ‖D w‖ :=
            norm_sub_norm_le _ _
          rw [norm_pow, norm_real, Real.norm_of_nonneg hr.le, norm_mul, norm_conj] at h1
          nlinarith [mul_le_mul_of_nonneg_right hρc (norm_nonneg (w - c)), norm_nonneg (w - c)]
        have hDsphere : ∀ w, ‖w - c‖ = r → ‖D w‖ = r * ‖w - ρ‖ := by
          intro w hw
          have e : D w = (w - c) * (starRingEnd ℂ) (w - ρ) := by
            have h1 : ((r : ℂ)) ^ 2 = (w - c) * (starRingEnd ℂ) (w - c) := by
              rw [mul_conj, normSq_eq_norm_sq, hw]; push_cast; ring
            simp only [hD, h1, map_sub]
            ring
          rw [e, norm_mul, norm_conj, hw]
        have hB₁ : ∀ w ∈ closedBall c r, ‖f₁ w‖ ≤ B := by
          intro w hw
          have hcl : closure (ball c r) = closedBall c r := closure_ball c hr.ne'
          refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball
            (hf₁diff.diffContOnCl_ball (closedBall_subset_ball hrR)) ?_ (hcl ▸ hw)
          intro v hv
          rw [frontier_ball c hr.ne', mem_sphere, dist_eq_norm] at hv
          have hvρ : 0 < ‖v - ρ‖ := by
            rw [norm_pos_iff, sub_ne_zero]
            rintro rfl
            linarith
          have h1 := congrArg norm (hfac v)
          rw [norm_mul, norm_mul, norm_mul, hDsphere v hv, norm_real,
            Real.norm_of_nonneg hr.le] at h1
          have h2 : ‖f₁ v‖ = ‖f v‖ := by
            have hpos : 0 < r * ‖v - ρ‖ := mul_pos hr hvρ
            have h1' : r * ‖v - ρ‖ * ‖f₁ v‖ = r * ‖v - ρ‖ * ‖f v‖ := by rw [← h1]; ring
            exact mul_left_cancel₀ hpos.ne' h1'
          rw [h2]
          exact hB v (by rw [mem_closedBall, dist_eq_norm, hv])
        have hf₁c : ‖f₁ c‖ * ‖c - ρ‖ = ‖f c‖ * r := by
          have h1 := congrArg norm (hfac c)
          simp only [hD, sub_self, mul_zero, sub_zero] at h1
          rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hr.le] at h1
          have : r * (‖f₁ c‖ * ‖c - ρ‖) = r * (‖f c‖ * r) := by
            linear_combination -h1
          exact mul_left_cancel₀ hr.ne' this
        have hf₁c_pos : 0 < ‖f₁ c‖ := by
          by_contra h0
          have h0' : ‖f₁ c‖ = 0 := le_antisymm (not_lt.1 h0) (norm_nonneg _)
          rw [h0', zero_mul] at hf₁c
          have : 0 < ‖f c‖ * r := mul_pos hfc' hr
          linarith
        have hf₁c_ne : f₁ c ≠ 0 := norm_pos_iff.1 hf₁c_pos
        have hf₁c_ge : ‖f c‖ * (r / r₂) ≤ ‖f₁ c‖ := by
          rw [← mul_div_assoc, div_le_iff₀ hr₂, ← hf₁c]
          exact mul_le_mul_of_nonneg_left hcρle hf₁c_pos.le
        have hBpos : 0 < B := hfc'.trans_le (hB c (mem_closedBall_self hr.le))
        have hE₁ : Real.log (B / ‖f₁ c‖) ≤ Real.log (B / ‖f c‖) - lam := by
          rw [hlam, ← Real.log_div (div_pos hBpos hfc').ne' (div_pos hr hr₂).ne']
          refine Real.log_le_log (div_pos hBpos hf₁c_pos) ?_
          rw [div_div]
          exact div_le_div_of_nonneg_left hBpos.le (mul_pos hfc' (div_pos hr hr₂)) hf₁c_ge
        have hzero₁ : ∀ w ∈ closedBall c r₂, f₁ w = 0 → w.re ≤ a := by
          intro w hw hw0
          refine hzero w hw ?_
          have h1 := hfac w
          rw [hw0, mul_zero] at h1
          have hDw : D w ≠ 0 := by
            rw [← norm_pos_iff]
            have hw' : ‖w - c‖ ≤ r₂ := by simpa [dist_eq_norm] using hw
            have := hDlow w
            nlinarith
          exact (mul_eq_zero.1 h1).resolve_right hDw
        have hih := ih f₁ hf₁diff hB₁ hf₁c_ne hzero₁ (by
          push_cast at hn
          linarith)
        -- logarithmic differentiation
        have hzc : ‖z - c‖ ≤ r₁ := by simpa [dist_eq_norm] using hz
        have hzR : z ∈ ball c R := by
          rw [mem_ball, dist_eq_norm]; linarith
        have hzr₂ : z ∈ closedBall c r₂ := by
          rw [mem_closedBall, dist_eq_norm]; linarith
        have hzρ : z - ρ ≠ 0 := by
          intro h0
          rw [sub_eq_zero] at h0
          rw [h0] at haz
          linarith
        have hfz : f z ≠ 0 := fun h0 ↦ by linarith [hzero z hzr₂ h0]
        have hDz_low : r * (r - r₂) ≤ ‖D z‖ := by
          have := hDlow z
          nlinarith
        have hDz : D z ≠ 0 := by
          rw [← norm_pos_iff]; linarith
        have hf₁z : f₁ z ≠ 0 := by
          intro h0
          have h1 := hfac z
          rw [h0, mul_zero] at h1
          exact (mul_ne_zero hfz hDz) h1
        have hd1 : HasDerivAt (fun w ↦ f w * D w)
            (deriv f z * D z + f z * -(starRingEnd ℂ) (ρ - c)) z := by
          have hDd : HasDerivAt D (-(starRingEnd ℂ) (ρ - c)) z := by
            have h := ((hasDerivAt_id z).sub_const c).const_mul ((starRingEnd ℂ) (ρ - c))
            have h' := h.const_sub ((r : ℂ) ^ 2)
            simpa [hD] using h'
          exact (hf.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt.mul hDd
        have hd2 : HasDerivAt (fun w ↦ r * (w - ρ) * f₁ w)
            (r * 1 * f₁ z + r * (z - ρ) * deriv f₁ z) z :=
          (((hasDerivAt_id z).sub_const ρ).const_mul (r : ℂ)).mul
            (hf₁diff.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
        have hfun : (fun w ↦ f w * D w) = fun w ↦ r * (w - ρ) * f₁ w := funext hfac
        rw [hfun] at hd1
        have hX := hd1.unique hd2
        have hY := hfac z
        have hident : deriv f z / f z =
            deriv f₁ z / f₁ z + (z - ρ)⁻¹ + (starRingEnd ℂ) (ρ - c) / D z := by
          field_simp
          linear_combination (f₁ z * (z - ρ)) * hX - (f₁ z + (z - ρ) * deriv f₁ z) * hY
        have hinv : 0 ≤ ((z - ρ)⁻¹).re := by
          rw [inv_re]
          refine div_nonneg ?_ (normSq_nonneg _)
          rw [sub_re]; linarith
        have hlast : ‖(starRingEnd ℂ) (ρ - c) / D z‖ ≤ K₁ := by
          rw [norm_div, norm_conj, hK₁]
          exact div_le_div₀ hr₂.le hρc hrr hDz_low
        have hlast' : -K₁ ≤ ((starRingEnd ℂ) (ρ - c) / D z).re := by
          have := abs_re_le_norm ((starRingEnd ℂ) (ρ - c) / D z)
          linarith [neg_abs_le ((starRingEnd ℂ) (ρ - c) / D z).re]
        rw [hident, add_re, add_re]
        have : K * Real.log (B / ‖f₁ c‖) ≤ K * (Real.log (B / ‖f c‖) - lam) :=
          mul_le_mul_of_nonneg_left hE₁ hK
        linarith
      · have hne : ∀ w ∈ ball c r₂, f w ≠ 0 := fun w hw h0 ↦
          hex ⟨w, ball_subset_closedBall hw, h0⟩
        have h1 := norm_deriv_div_le_of_forall_mem_ball_ne_zero hr₁ h12
          (hf.mono (ball_subset_ball (h2r.trans hrR).le)) hne
          (fun w hw ↦ hB w (ball_subset_closedBall (ball_subset_ball h2r.le hw))) hz
        rw [← hK₀] at h1
        have h2 : K₀ * Real.log (B / ‖f c‖) ≤ K * Real.log (B / ‖f c‖) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          rw [hKdef]
          have : 0 ≤ K₁ / lam := by positivity
          linarith
        have h3 := abs_re_le_norm (deriv f z / f z)
        linarith [neg_abs_le (deriv f z / f z).re]
  refine main (⌊Real.log (B / ‖f c‖) / lam⌋₊ + 1) f hf hB hfc hzero ?_
  have := Nat.lt_floor_add_one (Real.log (B / ‖f c‖) / lam)
  rw [div_lt_iff₀ hlam0] at this
  exact_mod_cast this

end Complex
