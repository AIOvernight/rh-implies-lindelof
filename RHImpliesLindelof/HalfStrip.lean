import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Phragmén–Lindelöf interpolation in a vertical half-strip

We prove a Phragmén–Lindelöf principle for functions of polynomial growth in the half-strip
`a ≤ re s ≤ b`, `1 ≤ im s`, and deduce the convexity (interpolation) bound for the growth
exponent: if `f` is `O(t ^ α)` on the left edge and `O(t ^ β)` on the right edge, then on the
vertical line `re s = σ` it is `O(t ^ e)`, where `e` interpolates linearly between `α` and `β`.

## Main results

* `PhragmenLindelof.norm_le_of_forall_mem_frontier_rectangle_norm_le`: the maximum modulus
  principle on a closed rectangle `[a, b] × [1, T]`.
* `PhragmenLindelof.vertical_halfStrip_of_rpow_growth`: a function of polynomial growth in the
  half-strip which is bounded by `M` on its boundary is bounded by `M` in the half-strip.
* `PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_vertical_halfStrip`: the interpolation
  bound described above.
-/

open Complex Set Filter Topology

/-- For `0 < re w`, `|arg w| ≤ π / 2 * (|im w| / re w)`. -/
theorem Complex.abs_arg_le_pi_div_two_mul_abs_im_div_re {w : ℂ} (hw : 0 < w.re) :
    |arg w| ≤ Real.pi / 2 * (|w.im| / w.re) := by
  have h1 : |arg w| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.2 hw.le
  have h2 : 2 / Real.pi * |arg w| ≤ Real.sin |arg w| := Real.mul_le_sin (abs_nonneg _) h1
  have h3 : Real.sin |arg w| = |w.im| / ‖w‖ := by
    have : Real.sin |arg w| = |Real.sin (arg w)| := by
      rcases abs_cases (arg w) with ⟨h, h'⟩ | ⟨h, h'⟩
      · rw [h, abs_of_nonneg]
        exact Real.sin_nonneg_of_nonneg_of_le_pi h' (arg_le_pi w)
      · rw [h, Real.sin_neg, abs_of_nonpos]
        exact Real.sin_nonpos_of_nonpos_of_neg_pi_le h'.le (neg_pi_lt_arg w).le
    rw [this, sin_arg, abs_div, abs_norm]
  have h4 : |w.im| / ‖w‖ ≤ |w.im| / w.re :=
    div_le_div_of_nonneg_left (abs_nonneg _) hw (re_le_norm w)
  have hpi := Real.pi_pos
  calc |arg w| = Real.pi / 2 * (2 / Real.pi * |arg w|) := by field_simp
    _ ≤ Real.pi / 2 * (|w.im| / w.re) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

namespace PhragmenLindelof

/-- The maximum modulus principle on the closed rectangle `[a, b] × [1, T]`: a function which
is differentiable on the rectangle and bounded by `M` on its four edges is bounded by `M` on the
whole rectangle. -/
theorem norm_le_of_forall_mem_frontier_rectangle_norm_le {g : ℂ → ℂ} {a b T M : ℝ}
    (hab : a < b) (hT : 1 < T)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → DifferentiableAt ℂ g s)
    (hedge : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → s.im ≤ T →
      (s.re = a ∨ s.re = b ∨ s.im = 1 ∨ s.im = T) → ‖g s‖ ≤ M)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) (h3 : 1 ≤ s.im) (h4 : s.im ≤ T) : ‖g s‖ ≤ M := by
  have hcl : closure (Ioo a b ×ℂ Ioo 1 T) = Icc a b ×ℂ Icc 1 T := by
    rw [closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hT.ne]
  have hbdd : Bornology.IsBounded (Ioo a b ×ℂ Ioo 1 T) :=
    Bornology.IsBounded.reProdIm (Metric.isBounded_Ioo a b) (Metric.isBounded_Ioo 1 T)
  have hdc : DiffContOnCl ℂ g (Ioo a b ×ℂ Ioo 1 T) := by
    constructor
    · intro z hz
      rw [mem_reProdIm] at hz
      exact (hd z hz.1.1.le hz.1.2.le hz.2.1.le).differentiableWithinAt
    · rw [hcl]
      intro z hz
      rw [mem_reProdIm] at hz
      exact (hd z hz.1.1 hz.1.2 hz.2.1).continuousAt.continuousWithinAt
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hdc ?_ ?_
  · intro z hz
    rw [frontier_reProdIm, closure_Ioo hab.ne, closure_Ioo hT.ne, frontier_Ioo hab,
      frontier_Ioo hT] at hz
    rcases hz with hz | hz
    · rw [mem_reProdIm] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rcases hz2 with h | h
      · exact hedge z hz1.1 hz1.2 h.ge (h.le.trans hT.le) (Or.inr (Or.inr (Or.inl h)))
      · rw [mem_singleton_iff] at h
        exact hedge z hz1.1 hz1.2 (h ▸ hT.le) h.le (Or.inr (Or.inr (Or.inr h)))
    · rw [mem_reProdIm] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rcases hz1 with h | h
      · exact hedge z h.ge (h.le.trans hab.le) hz2.1 hz2.2 (Or.inl h)
      · rw [mem_singleton_iff] at h
        exact hedge z (h ▸ hab.le) h.le hz2.1 hz2.2 (Or.inr (Or.inl h))
  · rw [hcl, mem_reProdIm]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- **Phragmén–Lindelöf principle** in the vertical half-strip `a ≤ re s ≤ b`, `1 ≤ im s`, for
functions of polynomial growth: if `g` is differentiable on the half-strip, satisfies
`‖g s‖ ≤ B * (im s) ^ N` there, and is bounded by `M` on the three edges, then it is bounded by
`M` on the whole half-strip. -/
theorem vertical_halfStrip_of_rpow_growth {g : ℂ → ℂ} {a b M B N : ℝ} (hab : a < b)
    (hM : 0 < M)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → DifferentiableAt ℂ g s)
    (hedge : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im →
      (s.re = a ∨ s.re = b ∨ s.im = 1) → ‖g s‖ ≤ M)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → ‖g s‖ ≤ B * s.im ^ N)
    {s₀ : ℂ} (h1 : a ≤ s₀.re) (h2 : s₀.re ≤ b) (h3 : 1 ≤ s₀.im) : ‖g s₀‖ ≤ M := by
  -- key: for every ε > 0, ‖g s₀‖ * exp (-ε * im s₀) ≤ M
  have key : ∀ ε : ℝ, 0 < ε → ‖g s₀‖ * Real.exp (-ε * s₀.im) ≤ M := by
    intro ε hε
    have hnorm : ∀ s : ℂ,
        ‖g s * Complex.exp (I * ε * s)‖ = ‖g s‖ * Real.exp (-ε * s.im) := by
      intro s
      rw [norm_mul, Complex.norm_exp]
      congr 2
      simp [mul_assoc]
    have htend := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero N ε hε).const_mul B
    rw [mul_zero] at htend
    have hev := htend.eventually (eventually_lt_nhds hM)
    obtain ⟨T, hT, hT1, hT2⟩ :=
      (hev.and ((eventually_gt_atTop s₀.im).and (eventually_gt_atTop 1))).exists
    have := norm_le_of_forall_mem_frontier_rectangle_norm_le
      (g := fun s => g s * Complex.exp (I * ε * s)) (M := M) hab hT2
      (fun s ha hb h1 => (hd s ha hb h1).mul (by fun_prop))
      (by
        intro s ha hb h1 hsT hcase
        rw [hnorm]
        have hexp : Real.exp (-ε * s.im) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        rcases hcase with h | h | h | h
        · calc ‖g s‖ * Real.exp (-ε * s.im) ≤ ‖g s‖ * 1 :=
                mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
            _ ≤ M := by rw [mul_one]; exact hedge s ha hb h1 (Or.inl h)
        · calc ‖g s‖ * Real.exp (-ε * s.im) ≤ ‖g s‖ * 1 :=
                mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
            _ ≤ M := by rw [mul_one]; exact hedge s ha hb h1 (Or.inr (Or.inl h))
        · calc ‖g s‖ * Real.exp (-ε * s.im) ≤ ‖g s‖ * 1 :=
                mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
            _ ≤ M := by rw [mul_one]; exact hedge s ha hb h1 (Or.inr (Or.inr h))
        · calc ‖g s‖ * Real.exp (-ε * s.im) ≤ (B * s.im ^ N) * Real.exp (-ε * s.im) :=
                mul_le_mul_of_nonneg_right (hgrowth s ha hb h1) (Real.exp_pos _).le
            _ = B * (T ^ N * Real.exp (-ε * T)) := by rw [h]; ring
            _ ≤ M := hT.le)
      h1 h2 h3 hT1.le
    rwa [hnorm] at this
  have htend : Tendsto (fun ε : ℝ => ‖g s₀‖ * Real.exp (-ε * s₀.im)) (𝓝[>] 0)
      (𝓝 (‖g s₀‖)) := by
    have hc : Continuous (fun ε : ℝ => ‖g s₀‖ * Real.exp (-ε * s₀.im)) := by fun_prop
    have := hc.tendsto 0
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

private theorem abs_add_mul_sub_le {a b α κ x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    |α + κ * (x - a)| ≤ |α| + |κ| * (b - a) := by
  calc |α + κ * (x - a)| ≤ |α| + |κ * (x - a)| := abs_add_le _ _
    _ = |α| + |κ| * (x - a) := by rw [abs_mul, abs_of_nonneg (sub_nonneg.2 ha)]
    _ ≤ |α| + |κ| * (b - a) := by
        gcongr

/-- On the half-strip, the real part of the exponent `-(α + κ * (s - a)) * log (-I * s)` of the
auxiliary multiplier is `-(α + κ * (re s - a)) * log (im s) + O(1)`. -/
private theorem abs_re_neg_mul_log_add_mul_log_im_le {a b α κ : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b)
    (ht : 1 ≤ s.im) :
    |(-(((α : ℂ) + (κ : ℂ) * (s - a)) * Complex.log (-I * s))).re
        + (α + κ * (s.re - a)) * Real.log s.im|
      ≤ (|α| + |κ| * (b - a)) * Real.log (max |a| |b| + 1)
        + |κ| * (max |a| |b| * (Real.pi / 2)) := by
  have ht0 : 0 < s.im := by linarith
  have hK : |s.re| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le a
      have := le_max_left |a| |b|
      linarith
    · have := le_abs_self b
      have := le_max_right |a| |b|
      linarith
  have hK0 : 0 ≤ max |a| |b| := (abs_nonneg _).trans hK
  have hnorm : ‖-I * s‖ = ‖s‖ := by simp
  have hre : (-(((α : ℂ) + (κ : ℂ) * (s - a)) * Complex.log (-I * s))).re
      = -((α + κ * (s.re - a)) * Real.log ‖s‖) + κ * (s.im * arg (-I * s)) := by
    simp only [neg_re, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, sub_re, sub_im,
      Complex.log_re, Complex.log_im, hnorm, zero_mul, sub_zero, zero_add, add_zero]
    ring
  have harg : s.im * |arg (-I * s)| ≤ max |a| |b| * (Real.pi / 2) := by
    have h := abs_arg_le_pi_div_two_mul_abs_im_div_re (w := -I * s) (by simpa using ht0)
    have h1 : (-I * s).re = s.im := by simp
    have h2 : (-I * s).im = -s.re := by simp
    rw [h1, h2, abs_neg] at h
    calc s.im * |arg (-I * s)| ≤ s.im * (Real.pi / 2 * (|s.re| / s.im)) :=
          mul_le_mul_of_nonneg_left h ht0.le
      _ = |s.re| * (Real.pi / 2) := by field_simp
      _ ≤ max |a| |b| * (Real.pi / 2) := by gcongr
  have hlog1 : Real.log s.im ≤ Real.log ‖s‖ :=
    Real.log_le_log ht0 ((le_abs_self _).trans (abs_im_le_norm s))
  have hlog2 : Real.log ‖s‖ ≤ Real.log s.im + Real.log (max |a| |b| + 1) := by
    rw [← Real.log_mul ht0.ne' (by positivity)]
    apply Real.log_le_log (norm_pos_iff.2 (by intro h; rw [h] at ht0; simp at ht0))
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ = |s.re| + s.im := by rw [abs_of_pos ht0]
      _ ≤ max |a| |b| * s.im + s.im := by nlinarith [abs_nonneg s.re]
      _ = s.im * (max |a| |b| + 1) := by ring
  have he := abs_add_mul_sub_le (α := α) (κ := κ) ha hb
  rw [hre]
  have heq : -((α + κ * (s.re - a)) * Real.log ‖s‖) + κ * (s.im * arg (-I * s))
      + (α + κ * (s.re - a)) * Real.log s.im
      = -((α + κ * (s.re - a)) * (Real.log ‖s‖ - Real.log s.im))
        + κ * (s.im * arg (-I * s)) := by ring
  rw [heq]
  calc |-((α + κ * (s.re - a)) * (Real.log ‖s‖ - Real.log s.im))
          + κ * (s.im * arg (-I * s))|
      ≤ |-((α + κ * (s.re - a)) * (Real.log ‖s‖ - Real.log s.im))|
          + |κ * (s.im * arg (-I * s))| := abs_add_le _ _
    _ = |α + κ * (s.re - a)| * (Real.log ‖s‖ - Real.log s.im)
          + |κ| * (s.im * |arg (-I * s)|) := by
        rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hlog1),
          abs_of_pos ht0]
    _ ≤ (|α| + |κ| * (b - a)) * Real.log (max |a| |b| + 1)
          + |κ| * (max |a| |b| * (Real.pi / 2)) := by
        have h0 : 0 ≤ Real.log ‖s‖ - Real.log s.im := sub_nonneg.2 hlog1
        have h1 : Real.log ‖s‖ - Real.log s.im ≤ Real.log (max |a| |b| + 1) := by linarith
        have hP : 0 ≤ |α| + |κ| * (b - a) := (abs_nonneg _).trans he
        gcongr

/-- **Phragmén–Lindelöf interpolation in a vertical half-strip**. Let `f` be differentiable on
the half-strip `a ≤ re s ≤ b`, `1 ≤ im s`, of polynomial growth `‖f s‖ ≤ C * (im s) ^ A` there.
If `‖f (a + t * I)‖ ≤ C * t ^ α` on the left edge and `‖f (b + t * I)‖ ≤ C * t ^ β` on the right
edge, then for every `σ ∈ [a, b]` there is a constant `C'` with
`‖f (σ + t * I)‖ ≤ C' * t ^ e` for all `t ≥ 1`, where
`e = α + (β - α) * (σ - a) / (b - a)` is the linear interpolation between `α` and `β`. -/
theorem exists_norm_le_mul_rpow_interp_of_vertical_halfStrip {f : ℂ → ℂ} {a b α β A C : ℝ}
    (hab : a < b)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → DifferentiableAt ℂ f s)
    (hgrow : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → ‖f s‖ ≤ C * s.im ^ A)
    (hleft : ∀ t : ℝ, 1 ≤ t → ‖f (a + t * I)‖ ≤ C * t ^ α)
    (hright : ∀ t : ℝ, 1 ≤ t → ‖f (b + t * I)‖ ≤ C * t ^ β)
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 1 ≤ t →
      ‖f (σ + t * I)‖ ≤ C' * t ^ (α + (β - α) * (σ - a) / (b - a)) := by
  have hC : 0 ≤ C := by
    have := hleft 1 le_rfl
    simp only [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  set κ : ℝ := (β - α) / (b - a) with hκ
  set Q : ℝ := (|α| + |κ| * (b - a)) * Real.log (max |a| |b| + 1)
        + |κ| * (max |a| |b| * (Real.pi / 2)) with hQ
  set E : ℂ → ℂ := fun s =>
    Complex.exp (-(((α : ℂ) + (κ : ℂ) * (s - a)) * Complex.log (-I * s))) with hE
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hEup : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im →
      ‖E s‖ ≤ Real.exp Q * s.im ^ (-(α + κ * (s.re - a))) := by
    intro s h1 h2 h3
    have := (abs_le.1 (abs_re_neg_mul_log_add_mul_log_im_le (α := α) (κ := κ) h1 h2 h3)).2
    rw [hE, Complex.norm_exp, Real.rpow_def_of_pos (by linarith), ← Real.exp_add,
      Real.exp_le_exp]
    linarith
  have hElo : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im →
      Real.exp (-Q) * s.im ^ (-(α + κ * (s.re - a))) ≤ ‖E s‖ := by
    intro s h1 h2 h3
    have := (abs_le.1 (abs_re_neg_mul_log_add_mul_log_im_le (α := α) (κ := κ) h1 h2 h3)).1
    rw [hE, Complex.norm_exp, Real.rpow_def_of_pos (by linarith), ← Real.exp_add,
      Real.exp_le_exp]
    linarith
  have hEd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → DifferentiableAt ℂ E s := by
    intro s h1 h2 h3
    have hlog : DifferentiableAt ℂ (fun z : ℂ => Complex.log (-I * z)) s :=
      DifferentiableAt.clog (by fun_prop)
        (mem_slitPlane_iff.2 (Or.inl (by simp; linarith)))
    have hL : DifferentiableAt ℂ (fun z : ℂ => (α : ℂ) + (κ : ℂ) * (z - a)) s := by fun_prop
    exact ((hL.mul hlog).neg).cexp
  have hcancel : ∀ (t e : ℝ), 1 ≤ t → t ^ e * t ^ (-e) = 1 := by
    intro t e ht
    rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
  have hQpos : 0 < Real.exp Q := Real.exp_pos Q
  -- bound on G = f * E
  have hG : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im →
      ‖f s * E s‖ ≤ C * Real.exp Q + 1 := by
    intro s₀ hs₁ hs₂ hs₃
    refine vertical_halfStrip_of_rpow_growth (g := fun s => f s * E s) (B := C * Real.exp Q)
      (N := |A| + (|α| + |κ| * (b - a))) hab (by positivity)
      (fun s h1 h2 h3 => (hd s h1 h2 h3).mul (hEd s h1 h2 h3)) ?_ ?_ hs₁ hs₂ hs₃
    · intro s h1 h2 h3 hcase
      have ht0 : 0 < s.im := by linarith
      have hup := hEup s h1 h2 h3
      rw [norm_mul]
      rcases hcase with h | h | h
      · have hs : s = (a : ℂ) + (s.im : ℂ) * I := by
          apply Complex.ext <;> simp [h]
        have hf := hleft s.im h3
        rw [← hs] at hf
        rw [h, sub_self, mul_zero, add_zero] at hup
        calc ‖f s‖ * ‖E s‖ ≤ (C * s.im ^ α) * (Real.exp Q * s.im ^ (-α)) :=
              mul_le_mul hf hup (norm_nonneg _) (by positivity)
          _ = C * Real.exp Q * (s.im ^ α * s.im ^ (-α)) := by ring
          _ = C * Real.exp Q := by rw [hcancel _ _ h3, mul_one]
          _ ≤ C * Real.exp Q + 1 := by linarith
      · have hs : s = (b : ℂ) + (s.im : ℂ) * I := by
          apply Complex.ext <;> simp [h]
        have hf := hright s.im h3
        rw [← hs] at hf
        have hβ : α + κ * (b - a) = β := by rw [hκ]; field_simp; ring
        rw [h, hβ] at hup
        calc ‖f s‖ * ‖E s‖ ≤ (C * s.im ^ β) * (Real.exp Q * s.im ^ (-β)) :=
              mul_le_mul hf hup (norm_nonneg _) (by positivity)
          _ = C * Real.exp Q * (s.im ^ β * s.im ^ (-β)) := by ring
          _ = C * Real.exp Q := by rw [hcancel _ _ h3, mul_one]
          _ ≤ C * Real.exp Q + 1 := by linarith
      · have hf := hgrow s h1 h2 h3
        rw [h, Real.one_rpow, mul_one] at hf
        rw [h, Real.one_rpow, mul_one] at hup
        calc ‖f s‖ * ‖E s‖ ≤ C * Real.exp Q := mul_le_mul hf hup (norm_nonneg _) hC
          _ ≤ C * Real.exp Q + 1 := by linarith
    · intro s h1 h2 h3
      have ht0 : 0 < s.im := by linarith
      have hup := hEup s h1 h2 h3
      have hf := hgrow s h1 h2 h3
      have he := abs_add_mul_sub_le (α := α) (κ := κ) h1 h2
      rw [norm_mul]
      calc ‖f s‖ * ‖E s‖
          ≤ (C * s.im ^ A) * (Real.exp Q * s.im ^ (-(α + κ * (s.re - a)))) :=
            mul_le_mul hf hup (norm_nonneg _) (by positivity)
        _ = C * Real.exp Q * s.im ^ (A + -(α + κ * (s.re - a))) := by
            rw [Real.rpow_add ht0]; ring
        _ ≤ C * Real.exp Q * s.im ^ (|A| + (|α| + |κ| * (b - a))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.rpow_le_rpow_of_exponent_le h3
            have := le_abs_self A
            have := neg_abs_le (α + κ * (s.re - a))
            linarith
  refine ⟨(C * Real.exp Q + 1) * Real.exp Q, by positivity, ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  have hexp : α + (β - α) * (σ - a) / (b - a) = α + κ * (σ - a) := by rw [hκ]; ring
  rw [hexp]
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have h1 : a ≤ s.re := by rw [hre]; exact hσa
  have h2 : s.re ≤ b := by rw [hre]; exact hσb
  have h3 : 1 ≤ s.im := by rw [him]; exact ht
  have hlo := hElo s h1 h2 h3
  have hg := hG s h1 h2 h3
  rw [norm_mul, hre, him] at *
  have hid : Real.exp (-Q) * t ^ (-(α + κ * (σ - a))) * (Real.exp Q * t ^ (α + κ * (σ - a)))
      = 1 := by
    have h := hcancel t (α + κ * (σ - a)) ht
    have h' : Real.exp (-Q) * Real.exp Q = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc _ = (Real.exp (-Q) * Real.exp Q)
          * (t ^ (α + κ * (σ - a)) * t ^ (-(α + κ * (σ - a)))) := by ring
      _ = 1 := by rw [h, h', mul_one]
  have hpos : 0 < Real.exp Q * t ^ (α + κ * (σ - a)) := by positivity
  calc ‖f s‖ = ‖f s‖ * (Real.exp (-Q) * t ^ (-(α + κ * (σ - a))))
        * (Real.exp Q * t ^ (α + κ * (σ - a))) := by rw [mul_assoc, hid, mul_one]
    _ ≤ ‖f s‖ * ‖E s‖ * (Real.exp Q * t ^ (α + κ * (σ - a))) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left hlo (norm_nonneg _)
    _ ≤ (C * Real.exp Q + 1) * (Real.exp Q * t ^ (α + κ * (σ - a))) :=
        mul_le_mul_of_nonneg_right hg hpos.le
    _ = (C * Real.exp Q + 1) * Real.exp Q * t ^ (α + κ * (σ - a)) := by ring

end PhragmenLindelof
