# RH ⇒ Lindelöf in Lean 4

A Lean 4 / Mathlib formalization of Littlewood's theorem: the Riemann Hypothesis implies the Lindelöf Hypothesis.

```lean
theorem lindelof_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atTop] fun t : ℝ => t ^ ε

theorem lindelof_atBot_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[Filter.atBot] fun t : ℝ => |t| ^ ε
```

`RiemannHypothesis` and `riemannZeta` are Mathlib's own definitions. The statements use nothing defined in this repository.

## What this is, and what it is not

- **It is a conditional theorem.** It says "if RH, then Lindelöf". It does not prove RH and does not prove Lindelöf.
- **The mathematics is classical.** The implication is usually attributed to Littlewood (1912); a textbook account is Chapter XIV of Titchmarsh, *The Theory of the Riemann Zeta-Function*. The contribution here is the machine-checked proof.
- **It covers ζ, as `t → +∞` and as `t → −∞`.** Dirichlet L-functions and Littlewood's sharper bound `exp(C log t / log log t)` are not included.
- **Novelty.** We searched Mathlib, the PrimeNumberTheoremAnd project (commit `a4fb698`, 2026-11-14), and GitHub code search, and found no existing Lean formalization of this implication. That is a bounded search, not a guarantee.

## Verification status

- `lake build` succeeds with Lean `v4.33.1` and Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`.
- `#print axioms` on both theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `@[extern]`, `opaque` or `set_option` anywhere in the sources.
- Replayed through the kernel with `leanchecker` (the checker bundled with the toolchain): all eight modules containing declarations pass. This re-checks the declarations of this repository and trusts the compiled Mathlib from the official cache.
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
```

To replay a module through the kernel (run one module at a time; do not pass the root module `RHImpliesLindelof`, which made the checker use tens of GB of memory in our runs):

```bash
lake env leanchecker RHImpliesLindelof.Main
```

## Proof outline

The route avoids the functional equation and Stirling's formula.

| File | Content |
|---|---|
| `Defs.lean` | Statements of the intermediate results |
| `Growth.lean` | `‖ζ(s)‖ ≤ 25·|Im s|` for `1/4 ≤ Re s ≤ 4`, `|Im s| ≥ 1`, from `ζ(s) = s/(s−1) − s∫₁^∞ {x} x^{−s−1} dx` |
| `LogZeta.lean` | Under RH, a holomorphic branch `g` of `log ζ` on discs centred at `2 + it`, with `‖g‖ ≤ C log t` by Borel–Carathéodory |
| `ThreeCircles.lean` | Hadamard's three-circles theorem, deduced from Mathlib's three-lines theorem |
| `Littlewood.lean` | Three circles give `‖g‖ ≤ C (log t)^a` with `a < 1`, hence `ζ(σ + it) ≪ t^ε` for each fixed `σ > 1/2` |
| `HalfStrip.lean` | A Phragmén–Lindelöf interpolation on a half-strip for functions of polynomial growth |
| `Final.lean` | Interpolate between `σ = 1/4` and `σ = 1/2 + η`, then let `η → 0` |
| `Main.lean` | The final statements, including `t → −∞` by conjugation symmetry |

`ThreeCircles.lean` and `HalfStrip.lean` are independent of ζ and may be useful on their own.

## How it was produced

The proof strategy and the interface between the pieces were written by Claude (Anthropic) in a Claude Code session directed by the repository owner; the individual Lean proofs were written by six Claude subagents working in parallel, and checked by the Lean kernel. No part of the Lean code was written or reviewed line by line by a human.

## Context

This was written on 2026-11-20, the day Levent Alpöge announced a Lean formalization of a proof of RH. This repository does not depend on that work and takes no position on its correctness: RH appears here only as a hypothesis.
