# Paper proof: RH implies `|ζ(1/2 + it)| ≤ exp(C log t / log log t)`

Notation: `L = log t`, `ℓ = log log t`, `s = σ + iτ`.

## 0. Why the originally planned route does not give the sharp bound

Plan: (a) three circles for a branch of `log ζ` to get `log|ζ(σ+it)| ≤ A L/ℓ` uniformly for
`σ ≥ 1/2 + 1/ℓ`; (b) convexity between `σ = 1/4` and `σ = 1/2 + 1/ℓ`.

Step (a) is not obtainable this way. The inputs of the method are only: `u = log|ζ|` is harmonic
in `σ > 1/2`, `u ≤ A L` there, `log ζ = O(1)` for `σ ≥ 1 + η`. The function
`g(s) = L · exp(-2ℓ (s - 1/2))` (a "Dirichlet monomial" `L² n^{-s}`, `n = L²`) satisfies all of
them (`Re g ≤ L`, `|g| ≤ 1` on `σ ≥ 1`) and `|g(1/2 + 1/ℓ)| = L e^{-2}`. So no argument using
only these inputs gives better than `O(L)` at `σ = 1/2 + 1/ℓ`. Concretely, with radii
`r₁ = σ₀-1-η`, `r₂ = σ₀-σ`, `r₃ = σ₀-1/2-δ`, three circles gives
`|log ζ| ≤ (C/η)^{1-a} (C σ₀ L/δ)^a` with `a = 1 - 2(σ-1/2) + O(δ+η+1/σ₀)`; this is `≤ A L/ℓ`
only when `L^{-2(σ-1/2)} ≤ δ/(σ₀ ℓ)`, i.e. for `σ ≥ 1/2 + c log ℓ/ℓ`. Feeding that into (b)
yields only `exp(C log t · log log log t / log log t)`. The loss is intrinsic to working with `log ζ`; the gain of `1/ℓ` appears when one works
with `ζ'/ζ` and integrates.

## 1. Route actually used

No branch of `log ζ`, no Phragmén–Lindelöf. Three steps.

### Step 1 (general lemma, Landau/Blaschke). 
Let `0 < r₁ < r₂ < r < R`. There is `K = K(r₁,r₂,r) ≥ 0` such that: if `f` is holomorphic on
`ball(c,R)`, `|f| ≤ B` on `closedBall(c,r)`, `f(c) ≠ 0`, and every zero `ρ` of `f` in
`closedBall(c,r₂)` has `Re ρ ≤ a`, then for all `z ∈ closedBall(c,r₁)` with `Re z > a`:
`Re (f'/f)(z) ≥ -K log(B/|f(c)|)`.

Proof. Put `E(f) = log(B/|f(c)|) ≥ 0`, `λ = r/r₂ > 1`,
`K₀ = 8 r₂/(r₂-r₁)²`, `K₁ = r₂/(r(r-r₂))`, `K = K₀ + K₁/log λ`.
Induction on `n` with `E(f) < n log λ` (for all `f`; `n = 0` is vacuous).

* No zero in `closedBall(c,r₂)`: `f` has a holomorphic logarithm `g` on `ball(c,r₂)`;
  `h = g - g(c)` has `h(c) = 0`, `Re h = log|f| - log|f(c)| ≤ E < M` for any `M > E`.
  Borel–Carathéodory on `ball(c,r₂)`, radius `ρ₁ = (r₁+r₂)/2`: `|h| ≤ 2Mρ₁/(r₂-ρ₁)` on
  `closedBall(c,ρ₁)`. Cauchy on the circle of radius `(r₂-r₁)/2` about `z`:
  `|f'/f(z)| = |h'(z)| ≤ 8Mρ₁/(r₂-r₁)² ≤ K₀ M`. Let `M ↓ E`.
* A zero `ρ ∈ closedBall(c,r₂)`, `p = ρ - c`: let `D(w) = r² - conj(p)(w-c)` (entire,
  `|D| ≥ r(r-r₂) > 0` on `closedBall(c,r)`, `|D(w)| = r|w-ρ|` on `|w-c| = r`) and
  `f₁ = dslope f ρ · D / r`, so `f · D = r (w-ρ) f₁`. Then `f₁` is holomorphic on `ball(c,R)`;
  `|f₁| = |f| ≤ B` on the sphere, hence on the closed ball (maximum principle);
  `|f₁(c)| = |f(c)| r/|p| ≥ λ |f(c)|`, so `E(f₁) ≤ E(f) - log λ`; zeros of `f₁` are zeros of `f`.
  By induction `Re f₁'/f₁(z) ≥ -K E(f₁)`. Logarithmic differentiation:
  `f'/f = f₁'/f₁ + 1/(z-ρ) + conj(p)/D(z)`; `Re 1/(z-ρ) > 0` since `Re z > a ≥ Re ρ`;
  `|conj(p)/D(z)| ≤ K₁`. Hence `Re f'/f(z) ≥ -K E(f) + K log λ - K₁ ≥ -K E(f)`.

### Step 2 (ζ'/ζ under RH).
(i) `|ζ(s)| ≤ e^{K₂}`, `|ζ(s)| ≥ e^{-K₂}` for `σ ≥ 3/2` (Euler product, existing lemma).
(ii) `|ζ'/ζ(s)| ≤ C₁ := 4 e^{2K₂}` for `σ ≥ 7/4` (Cauchy estimate on radius `1/4`, plus (i)).
(iii) For `τ ≥ 3`, `1/2 < σ ≤ 5/2`: `Re ζ'/ζ(s) ≥ -K (log(25(τ+2)) + K₂)`: Step 1 with
`c = 3/2 + iτ`, `(r₁,r₂,r,R) = (1, 9/8, 5/4, 11/8)`, `a = 1/2`, `B = 25(τ+2)` (existing
bound `|ζ| ≤ 25|Im s|` on `1/4 ≤ σ ≤ 4`), `|ζ(c)| ≥ e^{-K₂}`; zeros in the disc have real
part `1/2` by RH (the disc avoids `s = 1` and the trivial zeros).
In the form used: `Re ζ'/ζ(s) ≥ -A₁ log τ`, `A₁ = K(26 + K₂)` (as `25(τ+2) ≤ 25τ²`,
`log 25 ≤ 24 ≤ 24 log τ`).
(iv) Fix `t ≥ 100`, `M = A₀ L` with `A₀ = 2A₁ + C₁` (so `M ≥ C₁ L ≥ C₁` and
`A₁ log τ ≤ 2 A₁ L ≤ M` for `|τ - t| ≤ 3/2`, as `τ ≤ t²`). On `ball(2+it, 3/2)`: `Re F ≥ -M` where
`F = ζ'/ζ` ((iii) for `σ ≤ 7/4`, (ii) for `σ ≥ 7/4`). So `H = F/(F + 2M)` is holomorphic there
with `|H| ≤ 1`, and `|H| ≤ C₁/(2M - C₁) ≤ q := C₁/M ≤ 1` on `closedBall(2+it, 1/4)`.
Three circles, `r₁ = 1/4`, `r₂ = 3/2 - x`, `r₃ = 3/2 - x/2` (`0 < x ≤ 1`, `σ = 1/2 + x`):
`|H(σ+it)| ≤ q^{1-θ}`, `1 - θ = log(r₃/r₂)/log(r₃/r₁)`; `log(r₃/r₂) ≥ 1 - r₂/r₃ ≥ x/3` and
`log(r₃/r₁) ≤ r₃/r₁ - 1 ≤ 5`, so `1 - θ ≥ x/15` and `|H(σ+it)| ≤ q^{x/15}`. Since
`F = 2MH/(1-H)`: if `q^{x/15} ≤ 1/2` then `|F| ≤ 4M q^{x/15}`; otherwise
`-Re F ≤ M ≤ 4M q^{x/15}` anyway. Hence `-Re ζ'/ζ(1/2 + x + it) ≤ 4M q^{x/15}` for `0 < x ≤ 1`.

### Step 3 (integration).
`d/dσ log|ζ(σ+it)| = Re ζ'/ζ(σ+it)`. With `κ = log(1/q) = log(M/C₁) ≥ ℓ > 0` the function
`σ ↦ log|ζ(σ+it)| - (60M/κ) e^{-κ(σ-1/2)/15}` is non-decreasing on `(1/2, 3/2]`, so for
`0 < x < 1`: `log|ζ(1/2+x+it)| ≤ log|ζ(3/2+it)| + 60M/κ ≤ K₂ + 60 A₀ L/ℓ ≤ (K₂+60A₀) L/ℓ`
(as `L/ℓ ≥ 1`). Let `x → 0+` (continuity of `ζ` at `1/2 + it`). So `C = K₂ + 60 A₀`.

All constants (`K`, `K₂`, `C₁`, `A₁`, `A₀`, `C`) are absolute; the only `t`-dependence is `M = A₀ L`
and `q = C₁/M`.

## 2. Formalization status

Fully formalized, no `sorry`: Step 1 in `LogDerivLowerBound.lean`, Step 2 in
`LogDerivZeta.lean`, Step 3 and the final theorem in `Main.lean`.
