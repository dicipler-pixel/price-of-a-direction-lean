<div align="center">

# The Price of a Direction — Lean proofs

**The exact finite results of the paper, checked by the Lean kernel on every push.**

[![Lean proof check](https://github.com/dicipler-pixel/price-of-a-direction-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/price-of-a-direction-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-17-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21918463-blue)](https://doi.org/10.5281/zenodo.21918463)

Jeromie Beasley

</div>

---

## The idea in one line

A direction costs a channel. Two unit directions at angle θ overlap as `cos²θ` and are
separated by exactly `sin²θ`, so a family of directions stays resolvable only while every
pair clears the trackability threshold — and when two directions coalesce, the single
channels are lost while the pair's shared subspace survives.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Lemma 2.1 | `Tr(P_u P_v) = (u·v)² = cos²θ` and `½‖P_u − P_v‖²_F = 1 − (u·v)² = sin²θ` for unit directions; distinct trackable channels ⇔ `sin²θ ≥ ε` | `overlap`, `separation`, `trackable_iff` |
| Lemma 2.1 | Census depth `log(1/sin²δ) = 2 log(1/sin δ)` | `census_depth` |
| Prop. B.2 | `XY` and `YX` share every nonzero eigenvalue; for projectors, `spec(QPQ) \ {0} ⊆ spec(PQP) \ {0}` (and symmetrically) | `nonzero_eigen_swap`, `exchange_symmetry` |
| Thm. B.4 | `K = [[b, μ], [δ, b]]` has eigenvalues `b ± √(μδ)` with eigenvectors `(√μ, ±√δ)`; the two rank-one spectral projectors sum to the identity (the rank-two projector is constant) while their entries grow without bound as `δ → 0⁺` | `K_eigen`, `specProj_sum`, `specProj_entry_tendsto` |
| Prop. B.7 | Metric–curvature inequality `|Ω| ≤ 2√(g(V,V)g(W,W) − g(V,W)²)` | `metric_curvature` |
| Prop. B.8 | Wall link eigenvalues `g(I₁+I₂)/2 ± √D`, `D = (gΔI/2)² + 1 − e²`; real ⇔ `D ≥ 0`; complex ⇔ `e² > 1 + (gΔI/2)²` | `wall_charpoly`, `wall_real_iff`, `wall_complex_iff` |
| Prop. B.8 | Exact onset: complex ⇔ `ε²∂I² > ΔI² + 4/g²`, and `√(ΔI² + 4/g²) → |ΔI|` as `g → ∞`, so `ε* ≃ ΔI/|∂I|` at large gain | `onset_exact`, `onset_limit` |

The file is [`PriceOfDirection/Basic.lean`](PriceOfDirection/Basic.lean). What is not proved is
in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*The Price of a Direction: Boundary Channel Budgets, Directional Capacity, and Kakeya Structure
in Operator Transport*, Jeromie Beasley. DOI
[10.5281/zenodo.21918463](https://doi.org/10.5281/zenodo.21918463).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
