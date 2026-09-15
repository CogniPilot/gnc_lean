import Mathlib.Analysis.Matrix.Order

/-! Exact LMI certificates using mathlib's positive-semidefinite matrices.
Certificate construction can be analytic or external. Acceptance always
requires a kernel-checked equality and nonnegative weights; solver status,
floating-point eigenvalues, and `native_decide` are not proof oracles.
-/
noncomputable section
open Matrix
open scoped MatrixOrder Kronecker
namespace GNC.LMI
variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι]

/-- An exact weighted Gram/LDL certificate proves a negative LMI. -/
theorem of_weighted_gram [DecidableEq m] (M : Matrix n n ℝ)
    (L : Matrix m n ℝ) (d : m → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hfactor : -M = Lᴴ * diagonal d * L) : M ≤ 0 := by
  rw [Matrix.le_iff, zero_sub, hfactor]
  exact (Matrix.PosSemidef.diagonal hd).conjTranspose_mul_mul_same L

/-- Finite conic combinations of certified negative matrices are negative.
Convex combinations are a special case; no sample-grid argument is needed. -/
theorem nonpositive_sum (M : ι → Matrix n n ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hM : ∀ i, M i ≤ 0) :
    (∑ i, w i • M i) ≤ 0 := by
  rw [Matrix.le_iff, zero_sub, ← Finset.sum_neg_distrib]
  apply Matrix.posSemidef_sum
  intro i _
  have h : (-M i).PosSemidef := by simpa [Matrix.le_iff] using hM i
  simpa only [smul_neg] using h.smul (hw i)

/-- Completing the square certifies the scalar dissipative block exactly.
Its Kronecker product with I is the standard isotropic state/input LMI. -/
theorem dissipative_block {k κ : ℝ} (hκ : 0 < κ) (hk : κ ≤ k) :
    ( !![2*k-κ, -1; -1, 1/κ] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  · intro x
    simp [dotProduct, Fin.sum_univ_succ, Matrix.mulVec]
    have hs := sq_nonneg (κ*x 0-x 1)
    have hm := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg (x 0))
    have h := add_nonneg (div_nonneg hs hκ.le) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hm)
    convert h using 1 <;> field_simp <;> ring

/-- Dimension-independent isotropic certificate, inherited from mathlib's
Kronecker positivity theorem rather than a new PSD theory. -/
theorem dissipative_block_nd [DecidableEq n] {k κ : ℝ}
    (hκ : 0 < κ) (hk : κ ≤ k) :
    (( !![2*k-κ, -1; -1, 1/κ] : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ
      (1 : Matrix n n ℝ)).PosSemidef :=
  (dissipative_block hκ hk).kronecker Matrix.PosSemidef.one

end GNC.LMI
