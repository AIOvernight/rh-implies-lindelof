# Conductor-uniform Lindelöf bound on the critical line: paper proof

Target. For every `ε > 0` there is `C = C(ε)` such that for every `N ≥ 1`, every nontrivial
Dirichlet character `χ` mod `N` whose `L`-function has no zero in `re s > 1/2`, and every real
`t`,

    |L(1/2 + it, χ)| ≤ C · (N (|t| + 2))^ε.

Notation: `F = L(·, χ)` (entire since `χ ≠ 1`), `Q(t) = N (|t| + 2) ≥ 2`. "Absolute" means
independent of `N, χ, t` and of every other parameter.

Lean files: `UniformGrowth.lean` (Step 1), `UniformLog.lean` (Steps 2, 3 for an abstract
function), `UniformHalfLt.lean` (Step 3 for `L(s, χ)`), `Uniform.lean` (Steps 4, 5).

## Step 1. Uniform growth (`UniformGrowth.lean`)

Let `S(x) = Σ_{1 ≤ k ≤ x} χ(k)`; `|S(x)| ≤ N + 1` (`Dirichlet/Growth.lean`). For `re s > 0`,
`F(s) = s ∫_1^∞ S(x) x^{-s-1} dx` and `|∫| ≤ (N + 1)/re s`. Hence

* (G1) `|F(s)| ≤ |s| (N + 1)/re s` for all `re s > 0` (no restriction on `im s`).
* (G2) `|F(s)| ≤ 4 (N + 1) |s|` for `re s ≥ 1/4`.
* (G3) if `re s ≥ 1/2` and `|s − (2 + it)| < 3/2` then `|s| ≤ |re s| + |im s| ≤ 7/2 + |t| + 3/2`,
  so by (G1) and `N + 1 ≤ 2N`: `|F(s)| ≤ (|t| + 5) · 2N · 2 ≤ 10 N (|t| + 2) = 10 Q(t)`.
* (G4) if `re s = 1/4` then `|s| ≤ 1/4 + |im s|`, so
  `|F(s)| ≤ 4 · 2N · (1/4 + |im s|) ≤ 8 N (|im s| + 2)`.

Euler product (`Dirichlet/Main.lean`): for `re s ≥ 3/2`, `F(s) = exp(w)` with
`|w| ≤ K₀ := (3/2) Σ_p p^{-3/2}`, an absolute constant.

## Step 2. Uniform logarithm (`Lindelof.exists_log_norm_le_of_norm_le_exp`)

Abstract statement. Let `c ∈ ℂ`, `0 < δ < 1/4`, `M > 0`, `K ∈ ℝ`, and let `F` be holomorphic
and zero-free on `B = ball(c, 3/2 − δ)` with

* `|F| ≤ e^M` on `B`;
* for every `s ∈ ball(c, 1/2)` there is `w` with `e^w = F(s)`, `|w| ≤ K`.

Then there is `g` holomorphic on `B` with `e^g = F` on `B`,
`|g| ≤ 3 (M + K)/δ` on `closedBall(c, 3/2 − 2δ)` and `|g| ≤ 5K + 2` on `closedBall(c, 1/4)`.

Proof. `F'/F` is holomorphic on the disc `B`, so it has a primitive `g` there with
`g(c) = w_c` (the given logarithm at `c`, `|w_c| ≤ K`, so `K ≥ 0`). `(F e^{-g})' = 0` and
`F(c) e^{-g(c)} = 1`, so `e^g = F` on `B`. Consequently `re g = log|F| ≤ M` on `B`, and on
`ball(c, 1/2)`: `e^{re g} = |F| = e^{re w} ≤ e^K`, so `re g ≤ K < K + 1`.
Borel–Carathéodory for `g` (form: `|g(z)| ≤ 2 M' r/(R − r) + |g(c)| (R + r)/(R − r)` on
`closedBall(c, r)` when `re g ≤ M'` on `ball(c, R)`, `M' > 0`):

* `R = 3/2 − δ`, `r = 3/2 − 2δ`, `M' = M`: `|g| ≤ (2 M r + K (R + r))/δ ≤ 3 (M + K)/δ`
  (as `2r ≤ 3`, `R + r ≤ 3`);
* `R = 1/2`, `r = 1/4`, `M' = K + 1`: `|g| ≤ 2 (K + 1) + 3K = 5K + 2`.

No constant depends on `F` or `c`.

## Step 3. Three circles (`Lindelof.exists_norm_le_mul_exp_of_ne_zero`, then `L(s, χ)`)

Abstract statement. Given `0 < δ < 1/4`, `1/4 < r < 3/2 − 2δ`, `K`, `η > 0`, there is
`C = C(δ, r, K, η) > 0` such that for all `F, c` and all `M ≥ 1` satisfying the hypotheses of
Step 2: `|F(z)| ≤ C e^{ηM}` whenever `|z − c| = r`.

Proof. Put `K₁ = |K|`, `C₁ = max(5K₁ + 2, 3 (1 + K₁)/δ)`,
`a = log(4r)/log(4 (3/2 − 2δ)) ∈ (0, 1)`. With `g` from Step 2 (applied with `K₁`):
`|g| ≤ C₁` on the circle of radius `1/4`, and `|g| ≤ 3 (M + K₁)/δ ≤ C₁ M` on the circle of
radius `3/2 − 2δ` (as `M ≥ 1`). Hadamard's three circles theorem (inside the ball of radius
`3/2 − δ`): `|g(z)| ≤ C₁^{1−a} (C₁ M)^a = C₁ M^a`. Elementary: for `0 < a < 1` there is
`K₂ = K₂(C₁, η, a)` with `C₁ x^a ≤ η x + K₂` for all `x > 0`. So
`|F(z)| = e^{re g(z)} ≤ e^{K₂} e^{ηM}`; `C = e^{K₂}`.

Application (`DirichletCharacter.exists_norm_LFunction_le_mul_rpow_of_half_lt`). Fix
`1/2 < σ ≤ 1`, `η > 0`. Take `δ = (σ − 1/2)/4`, `r = 2 − σ` (then `1/4 < 1 ≤ r` and
`r < 3/2 − 2δ` because `σ > 1/2`), `K = K₀`, `c = 2 + it`, `M = log(10 Q(t))`
(`M ≥ 1` since `10 Q ≥ 20 > e`). On `ball(c, 3/2 − δ)`: `re s > 1/2 + δ`, so `F` is zero-free
by hypothesis and `|F| ≤ 10 Q = e^M` by (G3); on `ball(c, 1/2)`: `re s ≥ 3/2`, Euler product.
With `z = σ + it`, `|z − c| = 2 − σ`:

    |L(σ + it, χ)| ≤ C e^{η log(10 Q)} = C · 10^η · Q(t)^η      for all N, χ, t ∈ ℝ,

with `C · 10^η` depending only on `σ, η`.

## Step 4. From `re s = 1/2 + θ` to `re s = 1/2` (three lines, localised at `t₀`)

Route chosen: no half-strip, no reflection, no case split on `t`. Fix the target height `t₀`,
treat `Q = Q(t₀)` as a constant, and kill the growth in `|t − t₀|` by one linear denominator;
then the classical three lines theorem (for bounded functions, in Mathlib) applies on the whole
strip.

Abstract statement (`Lindelof.norm_le_mul_rpow_interp_of_vertical_strip`). Let `a < b`,
`0 ≤ η ≤ 1`, `Q ≥ 1`, `A, B > 0`, `t₀ ∈ ℝ`, and `f` holomorphic at each point of
`a ≤ re z ≤ b`, with

* `|f(z)| ≤ D (1 + |z|)` on the strip, for some `D` (any `D`; only used for boundedness);
* `|f(z)| ≤ A · Q · (1 + |im z − t₀|)` for `re z = a`;
* `|f(z)| ≤ B · Q^η · (1 + |im z − t₀|)` for `re z = b`.

Then for `z₀` with `a ≤ re z₀ ≤ b`, `im z₀ = t₀`:

    |f(z₀)| ≤ 2 max(A, B) · (re z₀ − a + 1) · Q^{1 + κ (re z₀ − a)},   κ = (η − 1)/(b − a).

Proof. Let `λ(z) = 1 + κ (z − a)` (so `λ(a) = 1`, `λ(b) = η`, `re λ(z) = 1 + κ (re z − a)`
since `κ, a` are real), `E(z) = exp(−λ(z) log Q)`, `d(z) = z − a + 1 − i t₀`, and
`G = f · E / d`. Then `|E(z)| = Q^{−(1 + κ (re z − a))}`; on the strip `re d = re z − a + 1 ≥ 1`
and `im d = im z − t₀`, hence `d ≠ 0`, `|d| ≥ 1` and `1 + |im z − t₀| ≤ 2 |d(z)|`.

* `re z = a`: `|G| ≤ A Q (1 + |im z − t₀|) Q^{-1}/|d| ≤ 2A`.
* `re z = b`: `|G| ≤ B Q^η (1 + |im z − t₀|) Q^{-η}/|d| ≤ 2B`.
* `G` is bounded on the closed strip: `κ ≤ 0`, so `1 + κ (re z − a) ≥ 1 + κ (b − a) = η ≥ 0`
  and `|E| ≤ 1` (as `Q ≥ 1`); `|z| ≤ |d| + |a − 1 + i t₀|` and `|d| ≥ 1` give
  `|f|/|d| ≤ D (2 + |a − 1 + i t₀|)`.

Three lines with both edge bounds `M = 2 max(A, B)`: `|G(z₀)| ≤ M^{1−x} M^x = M`. Finally
`d(z₀) = re z₀ − a + 1` (real, positive) and `|f(z₀)| = |G(z₀)| · |d(z₀)| / |E(z₀)|`.

The constant `2 max(A, B) (re z₀ − a + 1)` does not involve `Q`, `t₀`, `D`.

## Step 5. Assembly (`DirichletCharacter.exists_norm_LFunction_le_mul_rpow_uniform`)

Given `ε > 0` put `θ = min(ε/8, 1/2)`, `η = min(ε/2, 1)`, and let `C₁ = C₁(θ, η)` be the
constant of Step 3 for `σ = 1/2 + θ ∈ (1/2, 1]`. Fix `N, χ, t₀`, `Q = N (|t₀| + 2) ≥ 1`. For
all real `t`: `|t| + 2 ≤ (|t₀| + 2)(1 + |t − t₀|)`, i.e. `Q(t) ≤ Q (1 + |t − t₀|)`. So

* `re z = 1/4`: by (G4), `|F(z)| ≤ 8 Q(im z) ≤ 8 Q (1 + |im z − t₀|)`;
* `re z = 1/2 + θ`: by Step 3, `|F(z)| ≤ C₁ Q(im z)^η ≤ C₁ Q^η (1 + |im z − t₀|)^η
  ≤ C₁ Q^η (1 + |im z − t₀|)` (as `η ≤ 1`);
* (G2) gives the growth hypothesis with `D = 4 (N + 1)`.

Step 4 with `a = 1/4`, `b = 1/2 + θ`, `A = 8`, `B = C₁`, `z₀ = 1/2 + i t₀`:

    |F(1/2 + i t₀)| ≤ 2 max(8, C₁) · (5/4) · Q^{e},   e = 1 + (η − 1)(1/4)/(1/4 + θ).

`e = (θ + η/4)/(1/4 + θ) ≤ ε` because `θ + η/4 ≤ ε/8 + ε/8 = ε/4 ≤ ε (1/4 + θ)`. As `Q ≥ 1`,
`Q^e ≤ Q^ε`. Final constant: `C(ε) = 2 max(8, C₁(θ(ε), η(ε))) · 5/4`.

## Dependence of constants

`K₀` absolute; Step 2 constants explicit in `δ, M, K`; Step 3 constant depends on
`(δ, r, K, η)` only, hence on `(σ, η)` for `L`-functions; Step 4 constant is
`2 max(A, B)(re z₀ − a + 1)`; final constant depends on `ε` only. All `t ∈ ℝ` (including
`|t| < 1` and `t < 0`) are handled uniformly: the discs in Steps 2–3 are centred at `2 + it`
for arbitrary real `t` (possible because `F` is entire and (G1) holds for every `im s`), and
Step 4 works on the full vertical strip.
