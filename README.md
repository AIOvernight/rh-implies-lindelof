# Lindelöf from RH, in Lean 4

[![CI](https://github.com/AIOvernight/rh-implies-lindelof/actions/workflows/ci.yml/badge.svg)](https://github.com/AIOvernight/rh-implies-lindelof/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalization of results around the Lindelöf Hypothesis:

1. the Riemann Hypothesis implies the Lindelöf Hypothesis for ζ;
2. the Riemann Hypothesis implies Littlewood's sharper bound `|ζ(1/2 + it)| ≤ exp(C log |t| / log log |t|)`;
3. for a non-trivial Dirichlet character, non-vanishing of `L(s, χ)` for `Re s > 1/2` implies both bounds for `L(1/2 + it, χ)`;
4. the Lindelöf Hypothesis is equivalent to the bound `O(T^(1+ε))` for every even moment of ζ on the critical line (no hypothesis).

## Statements

```lean
theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε

theorem lindelof_atBot_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atBot] fun t : ℝ => |t| ^ ε

theorem exists_norm_riemannZeta_le_exp_log_div_log_log_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in Filter.atTop,
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (C * Real.log t / Real.log (Real.log t))

theorem DirichletCharacter.lindelof_of_LFunction_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hGRH : ∀ s : ℂ, 1 / 2 < s.re → LFunction χ s ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => LFunction χ (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε
```

together with `DirichletCharacter.lindelof_atBot_of_LFunction_ne_zero` for `t → −∞`, the sharper bound as `t → −∞` (`exists_norm_riemannZeta_le_exp_log_div_log_log_atBot_of_riemannHypothesis`), and the sharper bound for `L(s, χ)` in both directions (`DirichletCharacter.exists_norm_LFunction_le_exp_log_div_log_log`, `…_atBot`).

The equivalence with moments, which assumes nothing:

```lean
theorem lindelof_iff_integral_norm_riemannZeta_pow_isBigO :
    (∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε) ↔
    ∀ (k : ℕ) (ε : ℝ), 0 < ε →
      (fun T : ℝ => ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ (2 * k))
        =O[Filter.atTop] fun T : ℝ => T ^ (1 + ε)
```

`RiemannHypothesis`, `riemannZeta` and `DirichletCharacter.LFunction` are Mathlib's own definitions. The statements use nothing defined in this repository.

## What this is, and what it is not

- **Nothing here proves RH, GRH or Lindelöf.** Results 1–3 say "if there are no zeros with `Re s > 1/2`, then …". Result 4 is an equivalence between two open statements.
- **The mathematics is classical.** The implication RH ⇒ Lindelöf and the sharper bound are usually attributed to Littlewood; a textbook account is Chapter XIV of Titchmarsh, *The Theory of the Riemann Zeta-Function*. The contribution here is the machine-checked proof.
- **Scope.** For ζ and for a fixed non-trivial Dirichlet character: the Lindelöf bound and the sharper bound, as `t → ±∞`. For L-functions the implied constants depend on the character. Not included: uniformity in the conductor, and L-functions of higher degree. Of the classical equivalent forms of the Lindelöf Hypothesis only the one with moments is here (not Backlund's form in terms of zero counts, nor the implication to the density hypothesis).
- **Prior work.** Searched on 2026-11-21 in Mathlib and its pull requests, PrimeNumberTheoremAnd, [analytic-number-theory-lean](https://github.com/jonhanke/analytic-number-theory-lean), [Tau Ceti](https://github.com/TauCetiProject/TauCeti), about 130 GitHub repository searches and the Palomar registry. What already existed:
  - **The analytic engine.** Bounding a logarithm of a zero-free function on discs by Borel–Carathéodory and then interpolating (Hadamard) is in OpenAI's [math](https://github.com/openai/math) repository (`OAI.SevenEighths.LogarithmicControl`: `borel_caratheodory_closedBall`, `three_circles`, `logarithmic_control`), which predates this one. So the three-circles theorem is **not** new here; Mathlib itself has only the three-lines version.
  - **To the right of the critical line.** Qamar Munawer's [RiemannBlueprint](https://github.com/Qamarbajwa/RiemannBlueprint) proves, under RH, a bound `t^δ` for `1/ζ(s)` on `Re s ≥ σ₀ > 1/2` by the same method (and uses it for the Mertens function). [anaxia-research/Breakthrough-problems-3](https://github.com/anaxia-research/Breakthrough-problems-3) (`Vinogradov.CharSum.norm_bound`) proves, for a non-principal character with no zeros in `Re s > a + 2e`, a bound `(q(3 + |t|)²)^ε` for `L(s, χ)` and its inverse on `Re s ≥ a + 8e`, uniformly in the modulus. Those are Lindelöf-type bounds strictly to the right of `Re s = 1/2`.
  - **What we did not find anywhere:** the Lindelöf bound on the critical line itself (for ζ under RH, or for `L(s, χ)` under the corresponding hypothesis), and Littlewood's sharper bound `exp(C log t / log log t)`. That step, from `Re s > 1/2` to `Re s = 1/2`, and the sharper bound, are what this repository adds.
  - This is a bounded search, not a guarantee; in particular we have not asked on the Lean Zulip.

## Verification status

- `lake build` succeeds with Lean `v4.33.1` and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. CI rebuilds from scratch on every push, scans the sources for `sorry` and escape hatches, and fails if any main theorem uses a non-standard axiom.
- `#print axioms` on all nine theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `@[extern]`, `opaque` or `set_option` anywhere in the sources.
- Replayed through the kernel with `leanchecker` (the checker bundled with the toolchain): all sixteen modules containing declarations pass. This re-checks the declarations of this repository and trusts the compiled Mathlib from the official cache.
- Not yet reviewed by a human expert.

## How to check it yourself

```bash
lake exe cache get      # prebuilt Mathlib
lake build
lake env lean Check.lean
```

The last command prints one entry per main theorem (the last one wraps over three lines), each ending in

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

To replay a module through the kernel (run one module at a time; do not pass the root module `RHImpliesLindelof`, which made the checker use tens of GB of memory in our runs):

```bash
lake env leanchecker RHImpliesLindelof.Main
```

## Proof outline

**Lindelöf bound.** The argument is written once, for an abstract function `F`, and then applied to ζ and to `L(·, χ)`. It avoids the functional equation and Stirling's formula.

1. A crude polynomial bound for `F` in the strip `1/4 ≤ Re s ≤ 4`.
2. Since `F` has no zeros for `Re s > 1/2`, a holomorphic branch `g` of `log F` on discs centred at `2 + it`, with `‖g‖ ≤ C log t` by Borel–Carathéodory.
3. Hadamard's three-circles theorem gives `‖g‖ ≤ C (log t)^a` with `a < 1`, hence `F(σ + it) ≪ t^ε` for each fixed `σ > 1/2`.
4. A Phragmén–Lindelöf interpolation on a half-strip, between `σ = 1/4` and `σ = 1/2 + η`, letting `η → 0`.

**Moments.** If Lindelöf holds, integrate the bound. Conversely, `ζ'(1/2 + it) = O(t)` by a Cauchy estimate, so if `|ζ(1/2 + it)| = M` then `|ζ| ≥ M/2` on an interval of length about `M/t` after `t`; hence `M^(2k+1) ≪ t · ∫₁^(t+1) |ζ|^(2k)`, and letting `k → ∞` gives `M ≪ t^ε`.

**Sharper bound.** A different argument, through `ζ'/ζ` instead of `log ζ`: a lower bound `Re ζ'/ζ(s) ≥ −A log t` to the right of the critical line (a one-sided Landau lemma, dividing out zeros with Blaschke factors), its decay away from the line by three circles, and integration towards the line. A paper proof with all constants tracked is in `RHImpliesLindelof/Sharp/NOTES.md`.

| File | Content |
|---|---|
| `ThreeCircles.lean` | Hadamard's three-circles theorem (`Complex.norm_le_interp_of_mem_sphere`), deduced from Mathlib's three-lines theorem, for functions with values in a complex normed space |
| `HalfStrip.lean` | Phragmén–Lindelöf interpolation on a half-strip for functions of polynomial growth (`PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_vertical_halfStrip`) |
| `BorelCaratheodory.lean` | The Borel–Carathéodory theorem on a disc with arbitrary centre |
| `General.lean` | Steps 2–4 for an abstract `F`: `Lindelof.isBigO_rpow_of_ne_zero` |
| `Growth.lean` | `‖ζ(s)‖ ≤ 25·|Im s|` in the strip, from `ζ(s) = s/(s−1) − s∫₁^∞ {x} x^{−s−1} dx` |
| `LogZeta.lean` | Euler-product bound for `log ζ` on `Re s ≥ 3/2`; non-vanishing of ζ off the critical line under RH |
| `Main.lean` | The two Lindelöf theorems for ζ |
| `Dirichlet/Growth.lean` | `‖L(s, χ)‖ ≤ 20(N+1)·|Im s|` in the strip, from bounded partial sums of `χ` and Abel summation |
| `Dirichlet/Main.lean` | The two Lindelöf theorems for `L(s, χ)` |
| `Sharp/LogDerivLowerBound.lean` | One-sided Landau lemma: a lower bound for `Re f'/f` to the right of the zeros of `f` |
| `Sharp/LogDerivZeta.lean` | Under RH, the lower bound for `Re ζ'/ζ` and its decay away from the critical line |
| `Sharp/Main.lean` | The sharper bound for ζ |
| `Sharp/AtBot.lean` | The sharper bound for ζ as `t → −∞` |
| `Sharp/DirichletGeneral.lean` | The sharper bound for an abstract `F` (zero-free for `Re s > 1/2`, polynomial growth, bounded above and below for `Re s ≥ 3/2`) |
| `Sharp/DirichletMain.lean` | The sharper bound for `L(s, χ)` |
| `Moments.lean` | The Lindelöf Hypothesis is equivalent to `∫₁ᵀ |ζ(1/2 + it)|^(2k) dt = O(T^(1+ε))` for all `k` |

`ThreeCircles.lean`, `HalfStrip.lean`, `BorelCaratheodory.lean` and `Sharp/LogDerivLowerBound.lean` are general complex analysis: they do not mention ζ and import nothing from this repository beyond each other (the last one imports only `BorelCaratheodory.lean`).

## How it was produced

Everything in this repository was written by Claude (Anthropic) in a single Claude Code session directed by the repository owner. Claude chose the proof strategy and split the work; Claude subagents, several of them in parallel, wrote the Lean proofs, including the Dirichlet extensions, the sharper bound, the equivalence with moments and the two later refactors (towards Mathlib style, and to derive the ζ case from the abstract theorem). For the sharper bound the subagent found that the suggested route could not give the stated bound and replaced it with the `ζ'/ζ` argument above.

All of it was checked by the Lean kernel. **No part of the Lean code has been written or reviewed line by line by a human.**

## Context

This was written on 2026-11-20, the day Levent Alpöge announced a Lean formalization of a proof of RH and of GRH for Dirichlet L-functions. That announcement is the motivation: **assuming his proof is correct, the conclusions of the theorems in this repository follow.** His main theorem and our hypothesis for ζ are the same Mathlib statement, `RiemannHypothesis`, and his statement of non-vanishing of Dirichlet L-functions for `Re s > 1/2` gives our hypothesis `hGRH` for every `χ ≠ 1`; combining them is a one-line application in each case.

Two things should be kept apart:

- **What is proved here** is only the implications. They do not import his code and they remain true whether or not his proof is correct.
- **What we assume, and have not checked,** is the correctness of his proof. We have not built or audited his formalization, and we have not compiled the combination of the two. Until his proof is independently confirmed, the conclusions remain conditional.
