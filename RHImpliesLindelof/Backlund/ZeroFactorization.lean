import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Factoring out the zeros of a holomorphic function in a disc

Let `f` be holomorphic on `ball c R`, bounded by `B` on `closedBall c r` and with `f c ≠ 0`,
where `0 < r₂ < r < R`. We show that `f` factors on `ball c r` as
`f z = ∏ ρ ∈ Z, (z - ρ) * g z` where `Z` is a finite multiset of points of `closedBall c r₂`,
`g` is holomorphic on `ball c r` and zero-free on `closedBall c r₂`, and
`card Z * log (r / r₂) ≤ log (B / ‖f c‖)` (a Jensen-type bound for the number of zeros).
The proof removes the zeros one at a time by dividing by Blaschke factors of the disc of
radius `r`.

## Main definitions and results

* `Lindelof.IsZeroFactorization f c r₂ r Z g`: the factorisation statement.
* `Lindelof.IsZeroFactorization.count_eq_analyticOrderAt`: the multiplicity of `ρ` in `Z`
  is the order of vanishing of `f` at `ρ`.
* `Lindelof.IsZeroFactorization.finsum_toNat_analyticOrderAt_le_card` and
  `Lindelof.IsZeroFactorization.card_le_sum_finsum_toNat_analyticOrderAt`: comparison of
  `card Z` with sums of orders of vanishing over sets of zeros.
* `Lindelof.exists_isZeroFactorization`: existence of the factorisation, with the bound for
  `card Z`.
-/

open Metric Set Complex

namespace Lindelof

/-- The polynomial `∏ ρ ∈ Z, (w - ρ)` is differentiable in `w`. -/
theorem differentiable_multiset_prod_sub (Z : Multiset ℂ) :
    Differentiable ℂ fun w : ℂ ↦ (Z.map fun ρ ↦ w - ρ).prod := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (differentiable_id.sub_const ρ).mul ih

/-- The polynomial `∏ ρ ∈ Z, (z - ρ)` does not vanish away from `Z`. -/
theorem multiset_prod_sub_ne_zero (Z : Multiset ℂ) {z : ℂ} (hz : z ∉ Z) :
    (Z.map fun ρ ↦ z - ρ).prod ≠ 0 := by
  rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  rintro ⟨ρ, hρ, h0⟩
  exact hz (sub_eq_zero.1 h0 ▸ hρ)

/-- If every root is at distance at most `D` from `z`, then
`‖∏ ρ ∈ Z, (z - ρ)‖ ≤ D ^ card Z`. -/
theorem norm_multiset_prod_sub_le (Z : Multiset ℂ) {z : ℂ} {D : ℝ}
    (h : ∀ ρ ∈ Z, ‖z - ρ‖ ≤ D) : ‖(Z.map fun ρ ↦ z - ρ).prod‖ ≤ D ^ Z.card := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    have h1 := h ρ (Multiset.mem_cons_self ρ Z)
    have h2 := ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- If every root is at distance at least `d ≥ 0` from `z`, then
`d ^ card Z ≤ ‖∏ ρ ∈ Z, (z - ρ)‖`. -/
theorem pow_card_le_norm_multiset_prod_sub (Z : Multiset ℂ) {z : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ ρ ∈ Z, d ≤ ‖z - ρ‖) : d ^ Z.card ≤ ‖(Z.map fun ρ ↦ z - ρ).prod‖ := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    have h1 := h ρ (Multiset.mem_cons_self ρ Z)
    have h2 := ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)
    exact mul_le_mul h1 h2 (pow_nonneg hd _) (norm_nonneg _)

/-- `IsZeroFactorization f c r₂ r Z g` says that on `ball c r` the function `f` is the product
of the polynomial `∏ ρ ∈ Z, (z - ρ)`, whose roots lie in `closedBall c r₂`, and of a function
`g` holomorphic on `ball c r` without zeros in `closedBall c r₂`. -/
structure IsZeroFactorization (f : ℂ → ℂ) (c : ℂ) (r₂ r : ℝ) (Z : Multiset ℂ) (g : ℂ → ℂ) :
    Prop where
  /-- The points of `Z` lie in the smaller closed disc. -/
  mem_closedBall : ∀ ρ ∈ Z, ρ ∈ closedBall c r₂
  /-- The cofactor is holomorphic on the bigger open disc. -/
  differentiableOn : DifferentiableOn ℂ g (ball c r)
  /-- The factorisation. -/
  eq_prod_mul : ∀ z ∈ ball c r, f z = (Z.map fun ρ ↦ z - ρ).prod * g z
  /-- The cofactor has no zeros in the smaller closed disc. -/
  ne_zero : ∀ z ∈ closedBall c r₂, g z ≠ 0

namespace IsZeroFactorization

variable {f g : ℂ → ℂ} {c : ℂ} {r₂ r : ℝ} {Z : Multiset ℂ}

/-- Every point of `Z` is a zero of `f`. -/
theorem eq_zero_of_mem (h : IsZeroFactorization f c r₂ r Z g) (h2r : r₂ < r) {ρ : ℂ}
    (hρ : ρ ∈ Z) : f ρ = 0 := by
  rw [h.eq_prod_mul ρ (closedBall_subset_ball h2r (h.mem_closedBall ρ hρ))]
  refine mul_eq_zero_of_left (Multiset.prod_eq_zero ?_) _
  exact Multiset.mem_map.2 ⟨ρ, hρ, sub_self ρ⟩

/-- Every zero of `f` in `closedBall c r₂` belongs to `Z`. -/
theorem mem_of_eq_zero (h : IsZeroFactorization f c r₂ r Z g) (h2r : r₂ < r) {z : ℂ}
    (hz : z ∈ closedBall c r₂) (hfz : f z = 0) : z ∈ Z := by
  by_contra hzZ
  rw [h.eq_prod_mul z (closedBall_subset_ball h2r hz)] at hfz
  exact mul_ne_zero (multiset_prod_sub_ne_zero Z hzZ) (h.ne_zero z hz) hfz

/-- The multiplicity of `ρ` in `Z` is the order of vanishing of `f` at `ρ`. -/
theorem count_eq_analyticOrderAt (h : IsZeroFactorization f c r₂ r Z g) (h2r : r₂ < r) {ρ : ℂ}
    (hρ : ρ ∈ closedBall c r₂) : (Z.count ρ : ℕ∞) = analyticOrderAt f ρ := by
  classical
  have hρr : ρ ∈ ball c r := closedBall_subset_ball h2r hρ
  have hnhds : ball c r ∈ nhds ρ := isOpen_ball.mem_nhds hρr
  set Z' : Multiset ℂ := Z.filter fun x ↦ ¬x = ρ with hZ'
  set q : ℂ → ℂ := fun w ↦ (Z'.map fun x ↦ w - x).prod * g w with hq
  have hsplit : ∀ w : ℂ, (Z.map fun x ↦ w - x).prod =
      (w - ρ) ^ Z.count ρ * (Z'.map fun x ↦ w - x).prod := by
    intro w
    conv_lhs => rw [← Multiset.filter_add_not (fun x ↦ x = ρ) Z]
    rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
      Multiset.prod_replicate]
  have hqd : DifferentiableOn ℂ q (ball c r) :=
    (differentiable_multiset_prod_sub Z').differentiableOn.mul h.differentiableOn
  have hqa : AnalyticAt ℂ q ρ := hqd.analyticAt hnhds
  have hq0 : q ρ ≠ 0 := by
    refine mul_ne_zero (multiset_prod_sub_ne_zero Z' fun hmem ↦ ?_) (h.ne_zero ρ hρ)
    exact (Multiset.mem_filter.1 hmem).2 rfl
  have heq : ∀ᶠ w in nhds ρ, f w = (w - ρ) ^ Z.count ρ • q w := by
    filter_upwards [hnhds] with w hw
    rw [h.eq_prod_mul w hw, hsplit w, smul_eq_mul, hq, mul_assoc]
  have hfa : AnalyticAt ℂ f ρ := by
    have : AnalyticAt ℂ (fun w ↦ (w - ρ) ^ Z.count ρ • q w) ρ := by
      simp only [smul_eq_mul]
      exact ((analyticAt_id.sub analyticAt_const).pow _).mul hqa
    exact this.congr (heq.mono fun w hw ↦ hw.symm)
  exact (hfa.analyticOrderAt_eq_natCast.2 ⟨q, hqa, hq0, heq⟩).symm

/-- The multiplicity of `ρ` in `Z` is the order of vanishing of `f` at `ρ`, as a natural
number. -/
theorem count_eq_toNat_analyticOrderAt (h : IsZeroFactorization f c r₂ r Z g) (h2r : r₂ < r)
    {ρ : ℂ} (hρ : ρ ∈ closedBall c r₂) : Z.count ρ = (analyticOrderAt f ρ).toNat := by
  rw [← h.count_eq_analyticOrderAt h2r hρ, ENat.toNat_natCast]

/-- A set of zeros of `f` in `closedBall c r₂` is finite. -/
theorem finite_of_subset (h : IsZeroFactorization f c r₂ r Z g) (h2r : r₂ < r) {S : Set ℂ}
    (hS : S ⊆ closedBall c r₂) (hS0 : ∀ ρ ∈ S, f ρ = 0) : S.Finite := by
  classical
  exact Z.toFinset.finite_toSet.subset fun ρ hρ ↦
    Finset.mem_coe.2 (Multiset.mem_toFinset.2 (h.mem_of_eq_zero h2r (hS hρ) (hS0 ρ hρ)))

/-- The sum of the orders of vanishing of `f` over a set of zeros in `closedBall c r₂` is at
most `card Z`. -/
theorem finsum_toNat_analyticOrderAt_le_card (h : IsZeroFactorization f c r₂ r Z g)
    (h2r : r₂ < r) {S : Set ℂ} (hS : S ⊆ closedBall c r₂) (hS0 : ∀ ρ ∈ S, f ρ = 0) :
    ∑ᶠ ρ ∈ S, (analyticOrderAt f ρ).toNat ≤ Z.card := by
  classical
  have hfin := h.finite_of_subset h2r hS hS0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : hfin.toFinset ⊆ Z.toFinset := fun ρ hρ ↦
    Multiset.mem_toFinset.2
      (h.mem_of_eq_zero h2r (hS (hfin.mem_toFinset.1 hρ)) (hS0 ρ (hfin.mem_toFinset.1 hρ)))
  calc ∑ ρ ∈ hfin.toFinset, (analyticOrderAt f ρ).toNat
      = ∑ ρ ∈ hfin.toFinset, Z.count ρ :=
        Finset.sum_congr rfl fun ρ hρ ↦
          (h.count_eq_toNat_analyticOrderAt h2r (hS (hfin.mem_toFinset.1 hρ))).symm
    _ ≤ ∑ ρ ∈ Z.toFinset, Z.count ρ := Finset.sum_le_sum_of_subset hsub
    _ = Z.card := Multiset.toFinset_sum_count_eq Z

/-- If `Z` is covered by finitely many finite sets `S j`, then `card Z` is at most the sum over
`j` of the sums of the orders of vanishing of `f` over `S j`. -/
theorem card_le_sum_finsum_toNat_analyticOrderAt (h : IsZeroFactorization f c r₂ r Z g)
    (h2r : r₂ < r) {ι : Type*} (J : Finset ι) (S : ι → Set ℂ) (hfin : ∀ j, (S j).Finite)
    (hcov : ∀ ρ ∈ Z, ∃ j ∈ J, ρ ∈ S j) :
    Z.card ≤ ∑ j ∈ J, ∑ᶠ ρ ∈ S j, (analyticOrderAt f ρ).toNat := by
  classical
  calc Z.card = ∑ ρ ∈ Z.toFinset, Z.count ρ := (Multiset.toFinset_sum_count_eq Z).symm
    _ = ∑ ρ ∈ Z.toFinset, (analyticOrderAt f ρ).toNat :=
        Finset.sum_congr rfl fun ρ hρ ↦ h.count_eq_toNat_analyticOrderAt h2r
          (h.mem_closedBall ρ (Multiset.mem_toFinset.1 hρ))
    _ ≤ ∑ ρ ∈ Z.toFinset, ∑ j ∈ J, if ρ ∈ S j then (analyticOrderAt f ρ).toNat else 0 := by
        refine Finset.sum_le_sum fun ρ hρ ↦ ?_
        obtain ⟨j, hj, hρj⟩ := hcov ρ (Multiset.mem_toFinset.1 hρ)
        have := Finset.single_le_sum (f := fun j ↦ if ρ ∈ S j then
          (analyticOrderAt f ρ).toNat else 0) (fun _ _ ↦ Nat.zero_le _) hj
        simpa [hρj] using this
    _ = ∑ j ∈ J, ∑ ρ ∈ Z.toFinset, if ρ ∈ S j then (analyticOrderAt f ρ).toNat else 0 :=
        Finset.sum_comm
    _ ≤ ∑ j ∈ J, ∑ᶠ ρ ∈ S j, (analyticOrderAt f ρ).toNat := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin j), ← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset fun ρ hρ ↦ ?_
        exact (hfin j).mem_toFinset.2 (Finset.mem_filter.1 hρ).2

end IsZeroFactorization

/-- **Factorisation of a holomorphic function by its zeros in a disc.** Let `0 < r₂ < r < R`.
If `f` is holomorphic on `ball c R`, bounded by `B` on `closedBall c r` and `f c ≠ 0`, then `f`
factors on `ball c r` as `∏ ρ ∈ Z, (z - ρ) * g z` with `Z` a multiset of points of
`closedBall c r₂`, `g` zero-free on `closedBall c r₂`, and
`card Z * log (r / r₂) ≤ log (B / ‖f c‖)`. -/
theorem exists_isZeroFactorization {r₂ r R : ℝ} (hr₂ : 0 < r₂) (h2r : r₂ < r) (hrR : r < R)
    {f : ℂ → ℂ} {c : ℂ} {B : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hB : ∀ z ∈ closedBall c r, ‖f z‖ ≤ B) (hfc : f c ≠ 0) :
    ∃ (Z : Multiset ℂ) (g : ℂ → ℂ), IsZeroFactorization f c r₂ r Z g ∧
      (Z.card : ℝ) * Real.log (r / r₂) ≤ Real.log (B / ‖f c‖) := by
  have hr : 0 < r := hr₂.trans h2r
  set lam : ℝ := Real.log (r / r₂) with hlam
  have hlam0 : 0 < lam := Real.log_pos ((one_lt_div hr₂).2 h2r)
  -- induction on the number of zeros that may have to be removed
  have main : ∀ n : ℕ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball c R) →
      (∀ z ∈ closedBall c r, ‖f z‖ ≤ B) → f c ≠ 0 → Real.log (B / ‖f c‖) < n * lam →
      ∃ (Z : Multiset ℂ) (g : ℂ → ℂ), IsZeroFactorization f c r₂ r Z g ∧
        (Z.card : ℝ) * lam ≤ Real.log (B / ‖f c‖) := by
    intro n
    induction n with
    | zero =>
      intro f _ hB hfc hn
      have hfc' : 0 < ‖f c‖ := norm_pos_iff.2 hfc
      have : 0 ≤ Real.log (B / ‖f c‖) :=
        Real.log_nonneg ((one_le_div hfc').2 (hB c (mem_closedBall_self hr.le)))
      simp only [Nat.cast_zero, zero_mul] at hn
      linarith
    | succ n ih =>
      intro f hf hB hfc hn
      have hfc' : 0 < ‖f c‖ := norm_pos_iff.2 hfc
      have hE : 0 ≤ Real.log (B / ‖f c‖) :=
        Real.log_nonneg ((one_le_div hfc').2 (hB c (mem_closedBall_self hr.le)))
      by_cases hex : ∃ ρ ∈ closedBall c r₂, f ρ = 0
      · obtain ⟨ρ, hρ, hfρ⟩ := hex
        have hρc : ‖ρ - c‖ ≤ r₂ := by simpa [dist_eq_norm] using hρ
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
          simp only [hD]
          fun_prop
        have hf₁diff : DifferentiableOn ℂ f₁ (ball c R) :=
          (((differentiableOn_dslope hρR).2 hf).mul hDdiff.differentiableOn).div_const _
        have hDlow : ∀ w, r ^ 2 - r₂ * ‖w - c‖ ≤ ‖D w‖ := by
          intro w
          have h1 : ‖(r : ℂ) ^ 2‖ - ‖(starRingEnd ℂ) (ρ - c) * (w - c)‖ ≤ ‖D w‖ :=
            norm_sub_norm_le _ _
          rw [norm_pow, norm_real, Real.norm_of_nonneg hr.le, norm_mul, norm_conj] at h1
          nlinarith [mul_le_mul_of_nonneg_right hρc (norm_nonneg (w - c)), norm_nonneg (w - c)]
        have hDne : ∀ w ∈ closedBall c r, D w ≠ 0 := by
          intro w hw
          rw [← norm_pos_iff]
          have hw' : ‖w - c‖ ≤ r := by simpa [dist_eq_norm] using hw
          have := hDlow w
          nlinarith [norm_nonneg (w - c)]
        have hDsphere : ∀ w, ‖w - c‖ = r → ‖D w‖ = r * ‖w - ρ‖ := by
          intro w hw
          have e : D w = (w - c) * (starRingEnd ℂ) (w - ρ) := by
            have h1 : ((r : ℂ)) ^ 2 = (w - c) * (starRingEnd ℂ) (w - c) := by
              rw [mul_conj, normSq_eq_norm_sq, hw]
              push_cast
              ring
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
        obtain ⟨Z₁, g₁, hfact, hcard⟩ := ih f₁ hf₁diff hB₁ hf₁c_ne (by
          push_cast at hn
          linarith)
        have hDdiffOn : DifferentiableOn ℂ (fun w ↦ g₁ w * r / D w) (ball c r) :=
          (hfact.differentiableOn.mul_const _).div hDdiff.differentiableOn
            fun w hw ↦ hDne w (ball_subset_closedBall hw)
        refine ⟨ρ ::ₘ Z₁, fun w ↦ g₁ w * r / D w, ⟨?_, hDdiffOn, ?_, ?_⟩, ?_⟩
        · intro x hx
          rcases Multiset.mem_cons.1 hx with rfl | hx
          · exact hρ
          · exact hfact.mem_closedBall x hx
        · intro w hw
          have hDw := hDne w (ball_subset_closedBall hw)
          have h1 := hfac w
          rw [hfact.eq_prod_mul w hw] at h1
          simp only [Multiset.map_cons, Multiset.prod_cons]
          field_simp
          linear_combination h1
        · intro w hw
          have hwr : w ∈ closedBall c r := closedBall_subset_closedBall h2r.le hw
          exact div_ne_zero (mul_ne_zero (hfact.ne_zero w hw) hrC) (hDne w hwr)
        · rw [Multiset.card_cons]
          push_cast
          linarith
      · have hne : ∀ w ∈ closedBall c r₂, f w ≠ 0 := fun w hw h0 ↦ hex ⟨w, hw, h0⟩
        refine ⟨0, f, ⟨by simp, hf.mono (ball_subset_ball hrR.le), by simp, hne⟩, ?_⟩
        simpa using hE
  refine main (⌊Real.log (B / ‖f c‖) / lam⌋₊ + 1) f hf hB hfc ?_
  have := Nat.lt_floor_add_one (Real.log (B / ‖f c‖) / lam)
  rw [div_lt_iff₀ hlam0] at this
  exact_mod_cast this

end Lindelof
