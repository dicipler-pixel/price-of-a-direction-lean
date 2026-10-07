/-
The Price of a Direction (Jeromie Beasley, DOI 10.5281/zenodo.21918463): the exact finite
results of Lemma 2.1 and Appendix B.

* Lemma 2.1: for unit directions `u, v`, `Tr(P_u P_v) = (u·v)²` and
  `½‖P_u − P_v‖²_F = 1 − (u·v)²` (that is `cos²θ` and `sin²θ`); the census depth
  `log(1/sin²δ) = 2 log(1/sin δ)`.
* Proposition B.2: `XY` and `YX` share every nonzero eigenvalue; for projectors,
  `spec(QPQ) \ {0} = spec(PQP) \ {0}`.
* Theorem B.4: `K = [[b, μ], [δ, b]]` has eigenvalues `b ± √(μδ)` with eigenvectors
  `(√μ, ±√δ)`; the two rank-one spectral projectors sum to the identity (the rank-two cluster
  projector is constant) while their upper off-diagonal entries `±μ/(2√(μδ))` grow without
  bound in magnitude as `δ → 0⁺`.
* Proposition B.7: `|Ω| ≤ 2 √(g(V,V) g(W,W) − g(V,W)²)`.
* Proposition B.8: the wall link `h = [[g I₁, 1 + e], [1 − e, g I₂]]` has eigenvalues
  `g(I₁+I₂)/2 ± √D`, `D = (gΔI/2)² + 1 − e²`, which are real exactly when `D ≥ 0`; with
  `e = ½ ε g ∂I` the exact onset is `ε* = √(ΔI² + 4/g²)/|∂I|`, tending to `|ΔI|/|∂I|` as `g → ∞`.
-/
import Mathlib

namespace PriceOfDirection

open Matrix Finset Filter Topology

/-! ## Lemma 2.1: directions as channels -/

section Channels

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one projector onto a direction. -/
def proj (u : n → ℝ) : Matrix n n ℝ := vecMulVec u u

/-- Frobenius norm squared. -/
def frobSq (X : Matrix n n ℝ) : ℝ := trace (X * Xᵀ)

theorem trace_proj_mul (u v : n → ℝ) : trace (proj u * proj v) = (u ⬝ᵥ v) ^ 2 := by
  simp only [proj, trace, diag_apply, mul_apply, vecMulVec_apply, dotProduct, sq,
    sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem proj_transpose (u : n → ℝ) : (proj u)ᵀ = proj u := by
  ext i j
  simp [proj, vecMulVec_apply, mul_comm]

/-- **Lemma 2.1, overlap.** `Tr(P_u P_v) = cos²θ` with `cos θ = u·v`. -/
theorem overlap (u v : n → ℝ) : trace (proj u * proj v) = (u ⬝ᵥ v) ^ 2 := trace_proj_mul u v

/-- **Lemma 2.1, separation.** For unit directions, `½‖P_u − P_v‖²_F = 1 − (u·v)²`. -/
theorem separation (u v : n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    frobSq (proj u - proj v) / 2 = 1 - (u ⬝ᵥ v) ^ 2 := by
  unfold frobSq
  rw [transpose_sub, proj_transpose, proj_transpose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, trace_sub, trace_sub, trace_sub, trace_proj_mul, trace_proj_mul,
    trace_proj_mul, trace_proj_mul, hu, hv, dotProduct_comm v u]
  ring

/-- **Lemma 2.1, trackability.** Two unit directions are distinct trackable channels at
threshold `ε` exactly when `sin²θ = 1 − (u·v)² ≥ ε`. -/
theorem trackable_iff (u v : n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (ε : ℝ) :
    ε ≤ frobSq (proj u - proj v) / 2 ↔ ε ≤ 1 - (u ⬝ᵥ v) ^ 2 := by
  rw [separation u v hu hv]

end Channels

/-- **Lemma 2.1, census depth.** `log(1/sin²δ) = 2 log(1/sin δ)`. -/
theorem census_depth (δ : ℝ) :
    Real.log (1 / Real.sin δ ^ 2) = 2 * Real.log (1 / Real.sin δ) := by
  rw [one_div, one_div, ← inv_pow, Real.log_pow]
  push_cast
  ring

/-! ## Proposition B.2: exchange symmetry -/

section Exchange

variable {n m : Type*} [Fintype n] [Fintype m]

/-- `XY` and `YX` share every nonzero eigenvalue (one direction; the other is symmetric). -/
theorem nonzero_eigen_swap (X : Matrix n m ℝ) (Y : Matrix m n ℝ) (μ : ℝ) (hμ : μ ≠ 0)
    (v : n → ℝ) (hv : v ≠ 0) (h : (X * Y) *ᵥ v = μ • v) :
    Y *ᵥ v ≠ 0 ∧ (Y * X) *ᵥ (Y *ᵥ v) = μ • (Y *ᵥ v) := by
  refine ⟨fun h0 => ?_, ?_⟩
  · apply hv
    have : μ • v = 0 := by rw [← h, ← mulVec_mulVec, h0, mulVec_zero]
    exact (smul_eq_zero.mp this).resolve_left hμ
  · rw [mulVec_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, h, mulVec_smul]

/-- **Proposition B.2.** For idempotents `P, Q`, every nonzero eigenvalue of `QPQ` is an
eigenvalue of `PQP`. -/
theorem exchange_symmetry {k : Type*} [Fintype k] (P Q : Matrix k k ℝ) (hP : P * P = P)
    (hQ : Q * Q = Q) (μ : ℝ) (hμ : μ ≠ 0) (v : k → ℝ) (hv : v ≠ 0)
    (h : (Q * P * Q) *ᵥ v = μ • v) :
    ∃ w : k → ℝ, w ≠ 0 ∧ (P * Q * P) *ᵥ w = μ • w := by
  have h1 : Q * P * Q = (Q * P) * (P * Q) := by
    rw [show (Q * P) * (P * Q) = Q * (P * P) * Q by noncomm_ring, hP]
  have h2 : P * Q * P = (P * Q) * (Q * P) := by
    rw [show (P * Q) * (Q * P) = P * (Q * Q) * P by noncomm_ring, hQ]
  rw [h1] at h
  obtain ⟨hne, hw⟩ := nonzero_eigen_swap (Q * P) (P * Q) μ hμ v hv h
  exact ⟨_, hne, by rw [h2]; exact hw⟩

end Exchange

/-! ## Theorem B.4: trackability loss at a defective point -/

/-- `K(δ) = [[b, μ], [δ, b]]`. -/
def Kmat (b μ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![b, μ; δ, b]

/-- **Theorem B.4, spectrum.** `K (√μ, ±√δ) = (b ± √(μδ)) (√μ, ±√δ)`. -/
theorem K_eigen (b μ δ s : ℝ) (hμ : 0 ≤ μ) (hδ : 0 ≤ δ) (hs : s = 1 ∨ s = -1) :
    Kmat b μ δ *ᵥ ![Real.sqrt μ, s * Real.sqrt δ] =
      (b + s * Real.sqrt (μ * δ)) • ![Real.sqrt μ, s * Real.sqrt δ] := by
  have hm := Real.sq_sqrt hμ
  have hd := Real.sq_sqrt hδ
  have hmd : Real.sqrt (μ * δ) = Real.sqrt μ * Real.sqrt δ := Real.sqrt_mul hμ δ
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  ext i
  fin_cases i
  · simp [Kmat, mulVec, dotProduct, Fin.sum_univ_two, hmd]
    linear_combination (-(s * Real.sqrt δ)) * hm
  · simp [Kmat, mulVec, dotProduct, Fin.sum_univ_two, hmd]
    linear_combination (-Real.sqrt μ) * hd + (-(Real.sqrt μ * Real.sqrt δ ^ 2)) * hs2

/-- The spectral projector `R Lᵀ/(L·R)` for the eigenvalue `b + s√(μδ)`. -/
noncomputable def specProj (μ δ s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (2 * Real.sqrt (μ * δ))) •
    vecMulVec ![Real.sqrt μ, s * Real.sqrt δ] ![Real.sqrt δ, s * Real.sqrt μ]

/-- **Theorem B.4, the rank-two projector is constant.** For `μ, δ > 0` the two rank-one
spectral projectors sum to the identity. -/
theorem specProj_sum (μ δ : ℝ) (hμ : 0 < μ) (hδ : 0 < δ) :
    specProj μ δ 1 + specProj μ δ (-1) = 1 := by
  have hmd : Real.sqrt (μ * δ) = Real.sqrt μ * Real.sqrt δ := Real.sqrt_mul hμ.le δ
  have h1 : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have h2 : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [specProj, vecMulVec_apply, hmd] <;> field_simp <;> ring

/-- **Theorem B.4, the rank-one projectors blow up.** The upper off-diagonal entry of
`specProj μ δ s` is `s · μ/(2√(μδ))` (read off the definition), so it grows without bound in
magnitude as `δ → 0⁺`. The theorem is stated for `μ/(2√(μδ))`. -/
theorem specProj_entry_tendsto (μ : ℝ) (hμ : 0 < μ) :
    Tendsto (fun δ => μ / (2 * Real.sqrt (μ * δ))) (𝓝[>] 0) atTop := by
  have h0 : Tendsto (fun δ : ℝ => 2 * Real.sqrt (μ * δ)) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun δ : ℝ => 2 * Real.sqrt (μ * δ)) :=
        continuous_const.mul ((continuous_const.mul continuous_id).sqrt)
      have := hc.tendsto 0
      simp only [mul_zero, Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos hμ hδ))
  have := (tendsto_inv_nhdsGT_zero.comp h0).const_mul_atTop hμ
  refine this.congr (fun δ => ?_)
  simp [div_eq_mul_inv]

/-! ## Proposition B.7: the metric–curvature inequality -/

section Curvature

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Proposition B.7.** With `Q = g + (i/2)Ω` read as the inner product of the off-diagonal
blocks, `|Ω| ≤ 2 √(g(V,V) g(W,W) − g(V,W)²)`. -/
theorem metric_curvature (x y : E) :
    |2 * (⟪x, y⟫_ℂ).im| ≤ 2 * Real.sqrt (‖x‖ ^ 2 * ‖y‖ ^ 2 - (⟪x, y⟫_ℂ).re ^ 2) := by
  have hcs : (⟪x, y⟫_ℂ).re ^ 2 + (⟪x, y⟫_ℂ).im ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) x y
    have h2 : ‖⟪x, y⟫_ℂ‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by gcongr
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow] at h2
    nlinarith [h2]
  rw [abs_mul, abs_two]
  gcongr
  apply Real.abs_le_sqrt
  linarith

end Curvature

/-! ## Proposition B.8: the ratio gate -/

/-- The mean `m = g(I₁+I₂)/2` and discriminant `D = (gΔI/2)² + 1 − e²`. -/
theorem wall_charpoly (g I₁ I₂ e x : ℝ) :
    (g * I₁ - x) * (g * I₂ - x) - (1 + e) * (1 - e) =
      (x - g * (I₁ + I₂) / 2) ^ 2 - ((g * (I₂ - I₁) / 2) ^ 2 + 1 - e ^ 2) := by
  ring

/-- **Proposition B.8, reality.** The wall link has a real eigenvalue exactly when
`D = (gΔI/2)² + 1 − e² ≥ 0`. The witness is `g(I₁+I₂)/2 + √D`, and `wall_charpoly` writes
the polynomial as `(x − g(I₁+I₂)/2)² − D`. -/
theorem wall_real_iff (g I₁ I₂ e : ℝ) :
    (∃ x : ℝ, (g * I₁ - x) * (g * I₂ - x) - (1 + e) * (1 - e) = 0) ↔
      0 ≤ (g * (I₂ - I₁) / 2) ^ 2 + 1 - e ^ 2 := by
  constructor
  · rintro ⟨x, h⟩
    rw [wall_charpoly] at h
    nlinarith [sq_nonneg (x - g * (I₁ + I₂) / 2)]
  · intro hD
    refine ⟨g * (I₁ + I₂) / 2 + Real.sqrt ((g * (I₂ - I₁) / 2) ^ 2 + 1 - e ^ 2), ?_⟩
    rw [wall_charpoly, add_sub_cancel_left, Real.sq_sqrt hD, sub_self]

/-- **Proposition B.8, complex onset.** The eigenvalues are complex exactly when
`e² > 1 + (gΔI/2)²`. -/
theorem wall_complex_iff (g I₁ I₂ e : ℝ) :
    (¬ ∃ x : ℝ, (g * I₁ - x) * (g * I₂ - x) - (1 + e) * (1 - e) = 0) ↔
      1 + (g * (I₂ - I₁) / 2) ^ 2 < e ^ 2 := by
  rw [wall_real_iff, not_le]
  constructor <;> intro h <;> linarith

/-- **Proposition B.8, exact onset.** With `e = ½ ε g ∂I` (`g, ∂I ≠ 0`), the eigenvalues turn
complex exactly when `ε² ∂I² > ΔI² + 4/g²`. -/
theorem onset_exact (g ΔI dI ε : ℝ) (hg : g ≠ 0) :
    1 + (g * ΔI / 2) ^ 2 < (ε * g * dI / 2) ^ 2 ↔ ΔI ^ 2 + 4 / g ^ 2 < ε ^ 2 * dI ^ 2 := by
  have hg2 : 0 < g ^ 2 := by positivity
  constructor
  · intro h
    have : 4 + g ^ 2 * ΔI ^ 2 < g ^ 2 * (ε ^ 2 * dI ^ 2) := by nlinarith
    rw [← sub_pos] at this ⊢
    have key : ε ^ 2 * dI ^ 2 - (ΔI ^ 2 + 4 / g ^ 2) =
        (g ^ 2 * (ε ^ 2 * dI ^ 2) - (4 + g ^ 2 * ΔI ^ 2)) / g ^ 2 := by
      field_simp
      ring
    rw [key]
    positivity
  · intro h
    have h' : 4 / g ^ 2 < ε ^ 2 * dI ^ 2 - ΔI ^ 2 := by linarith
    rw [div_lt_iff₀ hg2] at h'
    nlinarith

/-- **Proposition B.8, large-gain limit.** The exact onset `√(ΔI² + 4/g²)` tends to `|ΔI|`
as `g → ∞`: for `gΔI ≫ 1` the onset `ε* ≃ |ΔI|/|∂I|` no longer depends on `g`. -/
theorem onset_limit (ΔI : ℝ) :
    Tendsto (fun g : ℝ => Real.sqrt (ΔI ^ 2 + 4 / g ^ 2)) atTop (𝓝 |ΔI|) := by
  have h : Tendsto (fun g : ℝ => ΔI ^ 2 + 4 / g ^ 2) atTop (𝓝 (ΔI ^ 2 + 0)) := by
    apply tendsto_const_nhds.add
    have := (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).comp (tendsto_id (α := ℝ))
    exact tendsto_const_nhds.div_atTop this
  rw [add_zero] at h
  have := (Real.continuous_sqrt.tendsto _).comp h
  rwa [Real.sqrt_sq_eq_abs] at this

end PriceOfDirection
