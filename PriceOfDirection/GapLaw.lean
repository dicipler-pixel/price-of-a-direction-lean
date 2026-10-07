/-
The Price of a Direction (Jeromie Beasley, DOI 10.5281/zenodo.21918463): the gap law behind
trackability, the tip and the tail.

A single direction (the tip) is held in place only by its gap to its nearest partner. A whole
subspace (the tail) is held in place by its gap to everything outside it, and that gap does not
involve the spacings inside the subspace at all. So the tip can swing freely inside the tail
while the tail stays put.

* `gap_identity`: if `A u = λ u`, `B v = μ v` and `B` is symmetric, then
  `(μ − λ)(v·u) = v·((B − A) u)`. This is one entry of the Sylvester equation behind the
  Davis–Kahan theorem.
* `tip_bound`: if the gap `|μ − λ|` is at least `δ > 0`, then
  `(v·u)² ≤ (v·((B − A) u))² / δ²`. The overlap of a new direction with an old one is bounded by
  coupling over gap, the squared form of the intrinsic metric `|Ḣ_mn|²/(E_n − E_m)²`.
* `tail_bound`: for families of eigenvectors `u_j` of `A` (inside) and `v_i` of `B` (outside)
  whose eigenvalues are separated by at least `δ`, the total squared overlap obeys
  `Σ_{i,j} (v_i·u_j)² ≤ Σ_{i,j} (v_i·((B − A) u_j))² / δ²`. Only inside-to-outside gaps enter
  the hypothesis; the spacings among the `u_j` themselves never do. With orthonormal families
  the left side is the squared Frobenius norm of `sin Θ` between the two subspaces.
* `tip_free_at_tie`: at an exact tie no gap holds the tip. For every `ε` the matrix
  `ε [[0, 1], [1, 0]]` has the eigenvector `(1, 1)` with eigenvalue `ε`, while `(1, 0)` is an
  eigenvector of the zero matrix, and their normalized overlap is `1/2`: the tip sits at 45° to
  where it was however small the coupling `ε` is.
-/
import Mathlib

namespace PriceOfDirection

open Matrix Finset

section GapLaw

variable {n : Type*} [Fintype n]

/-- **Gap identity.** If `A u = λ u`, `B v = μ v` and `Bᵀ = B`, then
`(μ − λ)(v·u) = v·((B − A) u)`. -/
theorem gap_identity (A B : Matrix n n ℝ) (hB : Bᵀ = B) (u v : n → ℝ) (lam mu : ℝ)
    (hu : A *ᵥ u = lam • u) (hv : B *ᵥ v = mu • v) :
    (mu - lam) * (v ⬝ᵥ u) = v ⬝ᵥ ((B - A) *ᵥ u) := by
  have hvB : v ᵥ* B = mu • v := by
    have h := vecMul_transpose B v
    rw [hB] at h
    rw [h, hv]
  rw [sub_mulVec, dotProduct_sub, dotProduct_mulVec, hvB, hu]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- **The tip bound.** If `|μ − λ| ≥ δ > 0`, the overlap obeys
`(v·u)² ≤ (v·((B − A) u))² / δ²`: coupling over gap. -/
theorem tip_bound (A B : Matrix n n ℝ) (hB : Bᵀ = B) (u v : n → ℝ) (lam mu δ : ℝ)
    (hu : A *ᵥ u = lam • u) (hv : B *ᵥ v = mu • v) (hδ : 0 < δ) (hgap : δ ≤ |mu - lam|) :
    (v ⬝ᵥ u) ^ 2 ≤ (v ⬝ᵥ ((B - A) *ᵥ u)) ^ 2 / δ ^ 2 := by
  have h2 : δ ^ 2 ≤ (mu - lam) ^ 2 := by
    nlinarith [sq_abs (mu - lam), abs_nonneg (mu - lam), mul_self_le_mul_self hδ.le hgap]
  rw [le_div_iff₀ (by positivity), ← gap_identity A B hB u v lam mu hu hv, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (v ⬝ᵥ u))]

/-- **The tail bound (Davis–Kahan, squared Frobenius form).** If every inside eigenvalue of `A`
is at least `δ` from every outside eigenvalue of `B`, the total squared overlap between the two
families is at most the total squared coupling over `δ²`. No gap among the inside directions
appears in the hypothesis. -/
theorem tail_bound {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix n n ℝ) (hB : Bᵀ = B)
    (U : κ → n → ℝ) (lamU : κ → ℝ) (V : ι → n → ℝ) (muV : ι → ℝ)
    (hU : ∀ j, A *ᵥ U j = lamU j • U j) (hV : ∀ i, B *ᵥ V i = muV i • V i) (δ : ℝ)
    (hδ : 0 < δ) (hgap : ∀ i j, δ ≤ |muV i - lamU j|) :
    ∑ i, ∑ j, (V i ⬝ᵥ U j) ^ 2 ≤ (∑ i, ∑ j, (V i ⬝ᵥ ((B - A) *ᵥ U j)) ^ 2) / δ ^ 2 := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun j _ =>
    tip_bound A B hB (U j) (V i) (lamU j) (muV i) δ (hU j) (hV i) hδ (hgap i j)

end GapLaw

/-- **The tip is free at a tie.** For every `ε`, `ε [[0, 1], [1, 0]]` has eigenvector `(1, 1)`
with eigenvalue `ε`, `(1, 0)` is an eigenvector of the zero matrix, and the normalized overlap
`(v·u)² / ((v·v)(u·u))` is `1/2`, so the angle is 45° however small `ε` is. -/
theorem tip_free_at_tie (ε : ℝ) :
    (ε • !![(0 : ℝ), 1; 1, 0]) *ᵥ ![1, 1] = ε • ![(1 : ℝ), 1] ∧
      (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0] = (0 : ℝ) • ![(1 : ℝ), 0] ∧
      (![(1 : ℝ), 1] ⬝ᵥ ![1, 0]) ^ 2 =
        (![(1 : ℝ), 1] ⬝ᵥ ![1, 1]) * (![(1 : ℝ), 0] ⬝ᵥ ![1, 0]) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  · simp
  · norm_num [dotProduct, Fin.sum_univ_two]

end PriceOfDirection
