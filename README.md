# RH ⇒ Lindelöf in Lean 4

[![CI](https://github.com/AIOvernight/rh-implies-lindelof/actions/workflows/ci.yml/badge.svg)](https://github.com/AIOvernight/rh-implies-lindelof/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalization of Littlewood's theorem: the Riemann Hypothesis implies the Lindelöf Hypothesis.

```lean
theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε

theorem lindelof_atBot_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atBot] fun t : ℝ => |t| ^ ε
```

The same for Dirichlet L-functions, assuming the corresponding zero-free half-plane:

```lean
theorem DirichletCharacter.lindelof_of_LFunction_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hGRH : ∀ s : ℂ, 1 / 2 < s.re → LFunction χ s ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => LFunction χ (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε
```

(and `DirichletCharacter.lindelof_atBot_of_LFunction_ne_zero` for `t → −∞`).

Littlewood's sharper bound for ζ:

```lean
theorem exists_norm_riemannZeta_le_exp_log_div_log_log_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in Filter.atTop,
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (C * Real.log t / Real.log (Real.log t))
```

`RiemannHypothesis`, `riemannZeta` and `DirichletCharacter.LFunction` are Mathlib's own definitions. The statements use nothing defined in this repository.

## What this is, and what it is not

- **It is a conditional theorem.** It says "if RH, then Lindelöf". It does not prove RH and does not prove Lindelöf.
- **The mathematics is classical.** The implication is usually attributed to Littlewood (1912); a textbook account is Chapter XIV of Titchmarsh, *The Theory of the Riemann Zeta-Function*. The contribution here is the machine-checked proof.
- **It covers ζ and Dirichlet L-functions of non-trivial characters, as `t → +∞` and as `t → −∞`.** For L-functions this is the `t`-aspect for a fixed character; the implied constant depends on the character. For ζ it also gives Littlewood's sharper bound `exp(C log t / log log t)` as `t → +∞`. The sharper bound for L-functions and the conductor aspect are not included.
- **Novelty.** We searched Mathlib, the PrimeNumberTheoremAnd project (commit `a4fb698`, 2026-11-14), and GitHub code search, and found no existing Lean formalization of this implication. That is a bounded search, not a guarantee.

## Verification status

- `lake build` succeeds with Lean `v4.33.1` and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. CI rebuilds from scratch on every push, scans the sources for `sorry` and escape hatches, and fails if any main theorem uses a non-standard axiom.
- `#print axioms` on all five theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `@[extern]`, `opaque` or `set_option` anywhere in the sources.
- Replayed through the kernel with `leanchecker` (the checker bundled with the toolchain): all twelve modules containing declarations pass. This re-checks the declarations of this repository and trusts the compiled Mathlib from the official cache.
- Not yet reviewed by a human expert.

## How to check it yourself

```bash
lake exe cache get      # prebuilt Mathlib
lake build
lake env lean Check.lean
```

Expected output of the last command:

```
'lindelof_of_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'lindelof_atBot_of_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirichletCharacter.lindelof_of_LFunction_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DirichletCharacter.lindelof_atBot_of_LFunction_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'exists_norm_riemannZeta_le_exp_log_div_log_log_of_riemannHypothesis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

To replay a module through the kernel (run one module at a time; do not pass the root module `RHImpliesLindelof`, which made the checker use tens of GB of memory in our runs):

```bash
lake env leanchecker RHImpliesLindelof.Main
```

## Proof outline

The route avoids the functional equation and Stirling's formula. The sharp bound uses a different argument, through `ζ'/ζ` instead of `log ζ`; a paper proof with all constants tracked is in `RHImpliesLindelof/Sharp/NOTES.md`.

| File | Content |
|---|---|
| `Growth.lean` | `‖ζ(s)‖ ≤ 25·|Im s|` for `1/4 ≤ Re s ≤ 4`, `|Im s| ≥ 1`, from `ζ(s) = s/(s−1) − s∫₁^∞ {x} x^{−s−1} dx` |
| `LogZeta.lean` | Under RH, a holomorphic branch `g` of `log ζ` on discs centred at `2 + it`, with `‖g‖ ≤ C log t` by Borel–Carathéodory |
| `ThreeCircles.lean` | Hadamard's three-circles theorem (`Complex.norm_le_interp_of_mem_sphere`), deduced from Mathlib's three-lines theorem |
| `Littlewood.lean` | Three circles give `‖g‖ ≤ C (log t)^a` with `a < 1`, hence `ζ(σ + it) ≪ t^ε` for each fixed `σ > 1/2` |
| `HalfStrip.lean` | A Phragmén–Lindelöf interpolation on a half-strip for functions of polynomial growth (`PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_vertical_halfStrip`) |
| `Main.lean` | Interpolate between `σ = 1/4` and `σ = 1/2 + η`, let `η → 0`; then `t → −∞` by conjugation symmetry |
| `Dirichlet/General.lean` | The same three steps for an abstract `F` that is holomorphic, of polynomial growth, zero-free for `Re s > 1/2` and has a bounded logarithm for `Re s ≥ 3/2` |
| `Dirichlet/Growth.lean` | `‖L(s, χ)‖ ≤ 20(N+1)·|Im s|` in the strip, from bounded partial sums of `χ` and Abel summation |
| `Dirichlet/Main.lean` | Euler-product logarithm bound and the two theorems for `L(s, χ)` |
| `Sharp/LogDerivLowerBound.lean` | A one-sided Landau lemma: a lower bound for `Re f'/f` to the right of the zeros of `f`, by dividing out zeros with Blaschke factors |
| `Sharp/LogDerivZeta.lean` | Under RH, `Re ζ'/ζ(s) ≥ −A log t` for `Re s > 1/2`, and its decay away from the critical line via three circles |
| `Sharp/Main.lean` | Integrate `Re ζ'/ζ` towards the critical line to get the sharp bound |

`ThreeCircles.lean` and `HalfStrip.lean` are independent of ζ and may be useful on their own. The three-circles theorem is stated for functions with values in any complex normed space.

## How it was produced

The proof strategy and the interface between the pieces were written by Claude (Anthropic) in a Claude Code session directed by the repository owner; the individual Lean proofs were written by six Claude subagents working in parallel, and checked by the Lean kernel. No part of the Lean code was written or reviewed line by line by a human.

## Context

This was written on 2026-11-20, the day Levent Alpöge announced a Lean formalization of a proof of RH. That announcement is the motivation: **assuming his proof is correct, the Lindelöf Hypothesis follows from the theorem in this repository.** His main theorem and our hypothesis are the same Mathlib statement, `RiemannHypothesis`, so combining the two is a one-line application. For Dirichlet L-functions, his statement of non-vanishing for `Re s > 1/2` gives our hypothesis `hGRH` for every `χ ≠ 1`.

Two things should be kept apart:

- **What is proved here** is only the implication RH ⇒ Lindelöf. It does not import his code and it remains true whether or not his proof is correct.
- **What we assume, and have not checked,** is the correctness of his proof. We have not built or audited his formalization, and we have not compiled the combination of the two. Until his proof is independently confirmed, Lindelöf remains conditional.
