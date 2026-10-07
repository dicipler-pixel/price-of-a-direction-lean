# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The analytic results are not formalized: the finite-cutoff dimension deficit (Theorem 4.1),
  the concentration alternative (Proposition 5.1), the capacity conjecture (3.1), the Lipschitz
  contour bound (Theorem B.3), the entropy integral `∫H = π²/3` (Lemma B.5) and the census
  coefficient (Theorem B.6).
* Theorem B.4's projectors are the explicit rank-one spectral projectors `R Lᵀ/(L·R)`; the Riesz
  contour definition is not used. Their idempotence `P² = P` and the relation `K P = λ P` are
  not proved as separate lemmas. `specProj_entry_tendsto` is stated for the scalar
  `μ/(2√(μδ))`, which is, up to the sign `s`, the upper off-diagonal entry of `specProj μ δ s`
  read off its definition.
* The measured capacities and the numerical scripts of Appendix A are numerical programs, not
  Lean proofs.
