import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# The Borel–Carathéodory theorem on a disc with arbitrary centre

Mathlib states the Borel–Carathéodory theorem for discs centred at the origin. This file
restates it for a disc with arbitrary centre `c`, on a closed sub-disc.

## Main results

* `Lindelof.borelCaratheodory_closedBall`: if `f` is holomorphic on `ball c R`, vanishes at `c`
  and has real part at most `M` there, then `‖f‖ ≤ 2 * M * r / (R - r)` on `closedBall c r`.
-/

open Complex Metric

namespace Lindelof

/-- The Borel–Carathéodory theorem on a disc centred at `c`: a bound for `‖f‖` on a closed
sub-disc in terms of an upper bound for `re f` on the disc and of `‖f c‖`. -/
lemma borelCaratheodory_closedBall {f : ℂ → ℂ} {c : ℂ} {M R r : ℝ} (hM : 0 < M)
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

end Lindelof
