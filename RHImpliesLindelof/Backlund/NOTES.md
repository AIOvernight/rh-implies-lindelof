# Backlund's reformulation of the Lindelöf hypothesis: paper proof

Reference: Titchmarsh, *The theory of the Riemann zeta-function*, §13.5 (Backlund 1918).
Status: fully formalised (no `sorry`) in `ZeroFactorization.lean` (§A), `Convexity.lean` (§B),
`ZeroCount.lean` (§C), `Local.lean` (§D), `Main.lean` (§E) of this directory.

## Statements

`LH` is the statement `∀ ε > 0, ζ(1/2 + it) = O(t^ε)` as `t → +∞`. For real `σ`, `T` let
`S(σ, T) = {ρ : ζ(ρ) = 0, σ < Re ρ, T < Im ρ ≤ T + 1}` and
`N(σ, T) = Σ_{ρ ∈ S(σ, T)} ord_ρ ζ` (zeros counted with multiplicity).

In Lean (`Main.lean`, root namespace; only Mathlib notions occur in the statements):

```lean
theorem riemannZeta_zeros_isLittleO_log_of_lindelof
    (h : ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε) :
    ∀ σ : ℝ, 1 / 2 < σ →
      (fun T : ℝ =>
        ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ T < ρ.im ∧ ρ.im ≤ T + 1},
          (analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℝ)) =o[Filter.atTop] Real.log

theorem lindelof_of_riemannZeta_zeros_isLittleO_log
    (h : ∀ σ : ℝ, 1 / 2 < σ →
      (fun T : ℝ =>
        ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ T < ρ.im ∧ ρ.im ≤ T + 1},
          (analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℝ)) =o[Filter.atTop] Real.log) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε

theorem lindelof_iff_riemannZeta_zeros_isLittleO_log :
    (∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε) ↔
    ∀ σ : ℝ, 1 / 2 < σ →
      (fun T : ℝ =>
        ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ σ < ρ.re ∧ T < ρ.im ∧ ρ.im ≤ T + 1},
          (analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℝ)) =o[Filter.atTop] Real.log
```

Remarks on the encoding.
* `∑ᶠ` over an infinite set is `0` by convention. For `σ > 1/2` and `T ≥ T₀(σ)` the set
  `S(σ, T)` is finite (C2 below), so for large `T` the expression is the genuine count; only
  large `T` matters for `=o[atTop]`.
* `analyticOrderAt ζ ρ : ℕ∞`, and `toNat ⊤ = 0`. For the zeros in question the order is finite
  and equals the multiplicity of `ρ` in the multiset of roots of §A (A3), so nothing is lost.
* The helper files use the abbreviations `Lindelof.zetaZeroBox σ T = S(σ, T)` and
  `Lindelof.zetaZeroCount σ T = N(σ, T)`, which unfold by definition to the expressions above.

Known facts used: `ζ` is holomorphic on `ℂ ∖ {1}`; `ζ(s) ≠ 0` for `Re s ≥ 1` (Mathlib);
`‖ζ(s)‖ ≤ 25 |Im s|` for `1/4 ≤ Re s ≤ 4`, `|Im s| ≥ 1` (G1, `Growth.lean`);
`e^{-K} ≤ ‖ζ(s)‖ ≤ e^{K}` for `Re s ≥ 3/2`, with an absolute `K ≥ 0` (G2,
`Sharp/LogDerivZeta.lean`);
Borel–Carathéodory on a disc `B(c, R)`: if `Re f ≤ M` (`M > 0`) then
`‖f‖ ≤ 2 M r/(R - r) + ‖f(c)‖ (R + r)/(R - r)` on `closedBall c r`; Hadamard's three-circles
theorem; the Phragmén–Lindelöf principle in a half-strip `a ≤ Re s ≤ b`, `Im s ≥ 1`
(`HalfStrip.lean`), in the two forms "bounded on the three edges + polynomial growth ⟹ bounded"
and "`O(t^α)` on the left edge, `O(t^β)` on the right edge + polynomial growth ⟹
`O(t^{α + (β - α)(σ - a)/(b - a)})` on `Re s = σ`".

## A. Factoring out the zeros in a disc — `ZeroFactorization.lean`

**A1 (`exists_isZeroFactorization`).** Let `0 < r₂ < r < R`, `f` holomorphic on `ball c R`,
`‖f‖ ≤ B` on `closedBall c r`, `f(c) ≠ 0`, `λ = log(r/r₂) > 0`, `E = log(B/‖f(c)‖) ≥ 0`. Then
there are a finite multiset `Z` of points of `closedBall c r₂` and `g` holomorphic on `ball c r`
with
1. `f(z) = ∏_{ρ ∈ Z} (z - ρ) · g(z)` on `ball c r`;
2. `g ≠ 0` on `closedBall c r₂`;
3. `card Z · λ ≤ E`.

*Proof.* Induction on `n` with `E < n λ` (`n = 0` is impossible as `E ≥ 0`). If `f` has no zero
in `closedBall c r₂`, take `Z = ∅`, `g = f`. Otherwise pick a zero `ρ` there, let
`D(w) = r² - conj(ρ - c)(w - c)` and `f₁ = dslope f ρ · D / r`, so `f D = r (w - ρ) f₁`. On the
circle `|w - c| = r` we have `D(w) = (w - c) conj(w - ρ)`, `|D(w)| = r |w - ρ|`, hence
`|f₁| = |f| ≤ B` there and, by the maximum principle, on `closedBall c r`. At the centre
`|f₁(c)| = |f(c)| r/|c - ρ| ≥ |f(c)| r/r₂`, so `E₁ := log(B/|f₁(c)|) ≤ E - λ < (n - 1) λ`. By
induction `f₁ = P₁ g₁` with `card Z₁ · λ ≤ E₁`. On `closedBall c r`, `|D| ≥ r² - r₂ r > 0`. Put
`Z = ρ :: Z₁`, `g = g₁ r / D`. ∎

**A2.** In the situation of A1: every `ρ ∈ Z` is a zero of `f`, and every zero of `f` in
`closedBall c r₂` belongs to `Z`.

**A3 (`count_eq_analyticOrderAt`).** For `ρ ∈ closedBall c r₂`: `count ρ Z = ord_ρ f` (write
`f = (z - ρ)^{count} · q` near `ρ` with `q = ∏_{ρ' ≠ ρ} (z - ρ') · g` analytic and nonzero at
`ρ`).

**A4.** If `S ⊆ closedBall c r₂` consists of zeros of `f`, then `S` is finite (`S ⊆ Z`) and
`Σ_{ρ ∈ S} ord_ρ f = Σ_{ρ ∈ S} count ρ Z ≤ card Z`.

**A5.** If `S_j` (`j ∈ J` finite) are finite sets with `Z ⊆ ⋃_j S_j`, then
`card Z = Σ_{ρ ∈ supp Z} ord_ρ f ≤ Σ_{j ∈ J} Σ_{ρ ∈ S_j} ord_ρ f`.

**A6.** If `|z - ρ| ≤ D` for all `ρ ∈ Z` then `|∏ (z - ρ)| ≤ D^{card Z}`; if `|z - ρ| ≥ d ≥ 0`
for all `ρ ∈ Z` then `|∏ (z - ρ)| ≥ d^{card Z}`.

## B. Convexity — `Convexity.lean`

**B1 (`exists_norm_riemannZeta_le_mul_im_rpow_of_isBigO`).** Let `η > 0` and
`ζ(1/2 + it) = O(t^η)`. Then there is `C` with `‖ζ(s)‖ ≤ C (Im s)^η` for all `s` with
`Re s ≥ 1/2`, `Im s ≥ 1`.

*Proof.* By continuity, `‖ζ(1/2 + it)‖ ≤ K₁ t^η` for all `t ≥ 1`. Put
`g(s) = ζ(s) exp(-η log(-is))`, holomorphic on `Im s > 0` (there `Re(-is) > 0`), with
`|g(s)| = |ζ(s)| |s|^{-η}` and `|s|^{-η} ≤ (Im s)^{-η} ≤ 1` for `Im s ≥ 1`. On the half-strip
`1/2 ≤ Re s ≤ 2`, `Im s ≥ 1`: `|g| ≤ K₁` on `Re s = 1/2`, `|g| ≤ e^K` on `Re s = 2` (G2),
`|g| ≤ 25` on `Im s = 1` (G1), and `|g| ≤ 25 Im s` throughout. By Phragmén–Lindelöf
`|g| ≤ M := K₁ + e^K + 25` in the half-strip, so
`|ζ(s)| ≤ M |s|^η ≤ M 3^η (Im s)^η` (as `|s| ≤ 2 + Im s ≤ 3 Im s`). For `Re s > 2`,
`|ζ(s)| ≤ e^K ≤ M 3^η (Im s)^η`. ∎

**B2 (`isBigO_riemannZeta_of_forall_half_lt`).** Suppose that for all `1/2 < σ ≤ 1` and `η > 0`
there is `C` with `‖ζ(σ + it)‖ ≤ C t^η` for `t ≥ 1`. Then LH holds.

*Proof.* Let `ε > 0`, `η = min(1/4, ε/16)`. Apply Phragmén–Lindelöf (second form) to `ζ` on
`1/4 ≤ Re s ≤ 1/2 + η`: exponent `1` on the left edge and in the interior (G1), exponent `ε/2`
on the right edge. At `σ = 1/2` the exponent is
`1 + (ε/2 - 1)(1/4)/(1/4 + η) = (η + ε/8)/(1/4 + η) ≤ ε` because `η ≤ ε/8`. ∎

## C. The zero count via Jensen — `ZeroCount.lean`

**C1 (`exists_zetaZeroCount_mul_le`).** Let `σ > 1/2`. There are `λ > 0`, `A > 0`, `T₀`, `K`
such that for all `T ≥ T₀` and all `B`: if `‖ζ(s)‖ ≤ B` whenever `Re s ≥ 1/2`,
`1 ≤ Im s ≤ T + A`, then `S(σ, T)` is finite and `N(σ, T) · λ ≤ log B + K`.

*Proof.* Let `u = σ - 1/2`, `A = 2 + σ + 1/u`, `c = A + i(T + 1/2)`, `r = A - 1/2`,
`r₂ = √((A - σ)² + 1/4)`, `R = A - 1/4`, `T₀ = A`, `λ = log(r/r₂)`, `K` as in G2.
* `r₂ < r`: `r² - (A - σ)² = u (2A - σ - 1/2) = u (7/2 + σ) + 2 > 1/4`.
* For `T ≥ A`: on `ball c R`, `Im s > T + 1/2 - R > 0`, so `ζ` is holomorphic there; on
  `closedBall c r`, `Re s ≥ A - r = 1/2` and `1 ≤ T + 1/2 - r ≤ Im s ≤ T + 1/2 + r = T + A`, so
  `‖ζ‖ ≤ B` there; `‖ζ(c)‖ ≥ e^{-K}` since `Re c = A ≥ 3/2`.
* `S(σ, T) ⊆ closedBall c r₂`: for `ρ ∈ S(σ, T)`, `σ < Re ρ < 1 < A` and
  `|Im ρ - (T + 1/2)| ≤ 1/2`, so `|ρ - c|² ≤ (A - σ)² + 1/4`.
By A1 and A4, `S(σ, T)` is finite and
`N(σ, T) λ ≤ card Z · λ ≤ log(B/‖ζ(c)‖) ≤ log B + K`. ∎

(A single disc of radius `< 3/2` centred at `2 + i(T + 1/2)` does not contain the whole box when
`σ ≤ 2 - √2`; this is why the centre is moved to the right, depending on `σ`.)

**C2 (`exists_finite_zetaZeroBox`).** For `σ > 1/2` and `T ≥ T₀(σ)`, `S(σ, T)` is finite: C1
with `B = 25 (T + A) + e^K` (G1 for `Re s ≤ 4`, G2 for `Re s > 4`).

**C3 (LH ⟹ few zeros; `zetaZeroCount_isLittleO_log_of_lindelof`).** Assume LH, let `σ > 1/2`
and `λ, A, T₀, K` as in C1. Let `ε > 0` and `η = ε λ/2`. By B1, `‖ζ(s)‖ ≤ C (Im s)^η` for
`Re s ≥ 1/2`, `Im s ≥ 1`; hence for `T ≥ max(T₀, A, 1)` the hypothesis of C1 holds with
`B = C (2T)^η`, and
`N(σ, T) λ ≤ log C + K + η log 2 + η log T`.
If moreover `log T ≥ (log C + K + η log 2)/η`, the right side is `≤ 2 η log T = ε λ log T`, so
`N(σ, T) ≤ ε log T`. ∎

## D. A bound for ζ in terms of nearby zeros — `Local.lean`

**D0 (`exists_differentiableOn_exp_eq_of_ne_zero`).** A zero-free holomorphic `g` on a disc
`ball c ρ` has a holomorphic logarithm `h` there with `h(c) = Log g(c)` (primitive of `g'/g`).

**D1 (`exists_norm_riemannZeta_le_exp_of_zetaZeroCount`).** Let `0 < δ ≤ 1/8`. There are
`C > 0`, `0 < a < 1`, `t₀` such that for every `t ≥ t₀` there is `n ∈ ℕ` with
`n ≤ Σ_{j=0}^{3} N(1/2 + δ, t - 2 + j)` and
`‖ζ(1/2 + 4δ + it)‖ ≤ exp( (C (1 + n))^{1-a} (C (log t + n))^a + 2n )`.

*Proof.* Constants: `K` from G2, `D = log(2/δ) > 0`,
`C = 5K + 14 + (3D + 3K + 33)/δ`,
`a = log((3/2 - 4δ)/(1/4)) / log((3/2 - 3δ)/(1/4))`,
`t₀ = max(3, T₀ + 2)` with `T₀` from C2 for `σ = 1/2 + δ`. Let `t ≥ t₀`, `L = log t ≥ 1`,
`c = 2 + it`.

*Factorisation.* `ζ` is holomorphic on `ball c (3/2)` and `‖ζ‖ ≤ B := 25 (t + 2)` on
`closedBall c (3/2 - δ)` (G1), `‖ζ(c)‖ ≥ e^{-K}`. By A1 with `r₂ = 3/2 - 2δ`, `r = 3/2 - δ`,
`R = 3/2`: `ζ = P g` on `ball c (3/2 - δ)`, `P(z) = ∏_{ρ ∈ Z} (z - ρ)`, `g` zero-free on
`closedBall c (3/2 - 2δ)`. Let `n = card Z`. Each `ρ ∈ Z` is a zero of `ζ` with
`1/2 + 2δ ≤ Re ρ < 1`, `|Im ρ - t| ≤ 3/2 - 2δ`, `|ρ - c| ≤ 3/2 - 2δ`.

*Count.* Each `ρ ∈ Z` has `Re ρ > 1/2 + δ` and `t - 2 < Im ρ ≤ t + 2`, so it lies in one of
`S(1/2 + δ, t - 2 + j)`, `j = 0, 1, 2, 3`; these are finite (C2, `t - 2 + j ≥ T₀`). By A5,
`n ≤ Σ_j N(1/2 + δ, t - 2 + j)`.

*Bound for `g`.* On the circle `|v - c| = 3/2 - 3δ/2`, `|v - ρ| ≥ δ/2` for `ρ ∈ Z`, so
`|P(v)| ≥ (δ/2)^n` and `|g(v)| ≤ B (2/δ)^n`; by the maximum principle this holds on
`closedBall c (3/2 - 3δ/2)`. Note `B ≤ t⁵ = e^{5L}` (`t ≥ 3`) and `(2/δ)^n = e^{nD}`.

*Logarithm.* Let `h` be the logarithm of `g` on `ball c (3/2 - 2δ)` with `h(c) = Log g(c)`
(D0), so `Re h = log|g|`. At the centre `1 ≤ |c - ρ| ≤ 3/2 ≤ e`, so `1 ≤ |P(c)| ≤ e^n`,
`|log|g(c)|| = |log|ζ(c)| - log|P(c)|| ≤ K + n`, and `|h(c)| ≤ K + n + π ≤ K + n + 4`.

*Large disc.* On `ball c (3/2 - 2δ)`, `Re h ≤ M := 5L + nD + 1`. Borel–Carathéodory with
`R = 3/2 - 2δ`, `r = 3/2 - 3δ`: on `closedBall c (3/2 - 3δ)`,
`|h| ≤ (2M (3/2 - 3δ) + |h(c)| (3 - 5δ))/δ ≤ (3M + 3(K + n + 4))/δ
     ≤ (3D + 3K + 33)(L + n)/δ ≤ C (L + n)`,
using `(3D + 3K + 33)(L + n) - 3M - 3(K + n + 4) = 3DL + 3K(L - 1) + 18(L - 1) + 3 + 3Kn + 30n ≥ 0`.

*Small disc.* On `ball c (1/2)`: `Re w ≥ 3/2`, so `|ζ(w)| ≤ e^K` and `|w - ρ| ≥ 1/2`,
`|P(w)| ≥ 2^{-n}`, `|g(w)| ≤ e^K 2^n ≤ e^{K + n}`, `Re h ≤ K + n + 1`. Borel–Carathéodory with
`R = 1/2`, `r = 1/4`: on `closedBall c (1/4)`,
`|h| ≤ 2(K + n + 1) + 3|h(c)| ≤ 5K + 5n + 14 ≤ (5K + 14)(1 + n) ≤ C (1 + n)`.

*Three circles.* With radii `1/4 < 3/2 - 4δ < 3/2 - 3δ` inside `ball c (3/2 - 2δ)`, at
`z₀ = 1/2 + 4δ + it` (`|z₀ - c| = 3/2 - 4δ`):
`|h(z₀)| ≤ (C (1 + n))^{1-a} (C (L + n))^a`.

*Conclusion.* `|z₀ - ρ| ≤ |z₀ - c| + |c - ρ| ≤ 3 ≤ e²`, so `|P(z₀)| ≤ e^{2n}` and
`|ζ(z₀)| = |P(z₀)| e^{Re h(z₀)} ≤ exp(|h(z₀)| + 2n)`. ∎

## E. Few zeros ⟹ LH, and the equivalence — `Main.lean`

**E1 (`exists_norm_riemannZeta_le_mul_rpow_of_zetaZeroCount_isLittleO`).** Assume
`N(σ, T) = o(log T)` for every `σ > 1/2`. Let `1/2 < σ ≤ 1` and `η > 0`. Then there is `C'` with
`‖ζ(σ + it)‖ ≤ C' t^η` for all `t ≥ 1`.

*Proof.* Let `δ = (σ - 1/2)/4 ∈ (0, 1/8]`, so `σ = 1/2 + 4δ`, and `C, a, t₀` as in D1. Put
`ε = min(1, η/4, (η/(4C))^{1/(1-a)})`, so `ε^{1-a} ≤ η/(4C)`. By hypothesis there is `T₁` with
`N(1/2 + δ, T) ≤ (ε/8) |log T|` for `T ≥ T₁`. Let
`t₁ = max(t₀, T₁ + 2, 3, e^{1/ε})` and `t ≥ t₁`, `L = log t`, so `ε L ≥ 1`. For `j ≤ 3`,
`1 ≤ t - 2 + j ≤ t²`, so `N(1/2 + δ, t - 2 + j) ≤ (ε/8) · 2L`, and the `n` of D1 satisfies
`n ≤ 4 (ε/8) 2L = ε L ≤ L`. Then `C (1 + n) ≤ 2CL ε`, `C (L + n) ≤ 2CL`, and
`(C (1 + n))^{1-a} (C (L + n))^a + 2n ≤ 2CL ε^{1-a} + 2 ε L ≤ (η/2) L + (η/2) L = η L`,
so `‖ζ(σ + it)‖ ≤ e^{ηL} = t^η`. For `1 ≤ t < t₁`, `‖ζ(σ + it)‖ ≤ 25 t ≤ 25 t₁ ≤ 25 t₁ t^η` (G1).
Take `C' = 25 t₁`. ∎

**E2 (few zeros ⟹ LH).** E1 and B2.

**E3 (equivalence).** C3 and E2.
