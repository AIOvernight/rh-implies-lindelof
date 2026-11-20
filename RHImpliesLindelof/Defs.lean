import Mathlib

/-!
# RH ⇒ Lindelöf: statements of the intermediate results
-/

open Complex

noncomputable section

namespace Lindelof

/-- The Lindelöf hypothesis for ζ (as `t → +∞`). -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε

/-- (P1) Crude polynomial bound for ζ in the strip `1/4 ≤ σ ≤ 4`, `|t| ≥ 1`. -/
def ZetaPolyGrowth : Prop :=
  ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * |s.im| ^ A

/-- (P2) Under RH: a holomorphic branch of `log ζ` on the disc of centre `2 + it` and radius `3/2 - δ`,
with `‖g‖ ≤ C log t` on the closed disc of radius `3/2 - 2δ` and `‖g‖ ≤ C` on the one of radius `1/4`. -/
def LogZetaBound : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 4 → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ t →
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball (2 + t * I) (3 / 2 - δ)) ∧
      (∀ s ∈ Metric.ball (2 + t * I) (3 / 2 - δ), Complex.exp (g s) = riemannZeta s) ∧
      (∀ s ∈ Metric.closedBall (2 + t * I) (3 / 2 - 2 * δ), ‖g s‖ ≤ C * Real.log t) ∧
      (∀ s ∈ Metric.closedBall (2 + t * I) (1 / 4), ‖g s‖ ≤ C)

/-- (P3) Hadamard's three-circles theorem. -/
def ThreeCircles : Prop :=
  ∀ (g : ℂ → ℂ) (c : ℂ) (r₁ r₂ r₃ R M₁ M₃ : ℝ),
    0 < r₁ → r₁ < r₂ → r₂ < r₃ → r₃ < R → 0 < M₁ → 0 < M₃ →
    DifferentiableOn ℂ g (Metric.ball c R) →
    (∀ z, dist z c = r₁ → ‖g z‖ ≤ M₁) →
    (∀ z, dist z c = r₃ → ‖g z‖ ≤ M₃) →
    ∀ z, dist z c = r₂ →
      ‖g z‖ ≤ M₁ ^ (1 - Real.log (r₂ / r₁) / Real.log (r₃ / r₁)) *
        M₃ ^ (Real.log (r₂ / r₁) / Real.log (r₃ / r₁))

/-- (P4) Littlewood: `ζ(σ + it) ≪ t^ε` for fixed `1/2 < σ ≤ 1`. -/
def ZetaSmallRightOfHalf : Prop :=
  ∀ σ ε : ℝ, 1 / 2 < σ → σ ≤ 1 → 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 3 ≤ t →
    ‖riemannZeta (σ + t * I)‖ ≤ C * t ^ ε

/-- (P5) Half-strip interpolation (Phragmén–Lindelöf with polynomial growth). -/
def HalfStripInterpolation : Prop :=
  ∀ (f : ℂ → ℂ) (a b α β A C : ℝ), a < b →
    (∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → DifferentiableAt ℂ f s) →
    (∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ s.im → ‖f s‖ ≤ C * s.im ^ A) →
    (∀ t : ℝ, 1 ≤ t → ‖f (a + t * I)‖ ≤ C * t ^ α) →
    (∀ t : ℝ, 1 ≤ t → ‖f (b + t * I)‖ ≤ C * t ^ β) →
    ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 1 ≤ t →
      ‖f (σ + t * I)‖ ≤ C' * t ^ (α + (β - α) * (σ - a) / (b - a))

end Lindelof
