import GNC.Estimation.CovariancePropagation
import Mathlib.Data.Real.StarOrdered

noncomputable section
open Matrix
namespace GNC.Estimation.KalmanCorrection

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

def posterior (P : Matrix n n ℝ) (B K : Matrix n m ℝ)
    (S : Matrix m m ℝ) : Matrix n n ℝ :=
  P - K * Bᵀ - B * Kᵀ + K * S * Kᵀ

theorem generalized_joseph (P : Matrix n n ℝ) (H : Matrix m n ℝ)
    (R : Matrix m m ℝ) (C K : Matrix n m ℝ) (hP : Pᵀ = P) :
    (1 - K * H) * P * (1 - K * H)ᵀ + K * R * Kᵀ
      - (1 - K * H) * C * Kᵀ - K * Cᵀ * (1 - K * H)ᵀ =
    posterior P (P * Hᵀ + C) K
      (H * P * Hᵀ + H * C + Cᵀ * Hᵀ + R) := by
  simp only [posterior, transpose_sub, transpose_one, transpose_mul,
    transpose_add, transpose_transpose, hP, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.add_mul, Matrix.mul_add, one_mul, mul_one, Matrix.mul_assoc]
  abel

omit [Fintype n] [DecidableEq n] in
theorem gain_gap (P : Matrix n n ℝ) (B K Kopt : Matrix n m ℝ)
    (S : Matrix m m ℝ) (hS : Sᵀ = S) (hopt : Kopt * S = B) :
    posterior P B K S - posterior P B Kopt S =
      (K - Kopt) * S * (K - Kopt)ᵀ := by
  rw [← hopt]
  simp only [posterior, transpose_mul, hS, transpose_sub, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [DecidableEq n] in
theorem gain_gap_positive_semidefinite (P : Matrix n n ℝ)
    (B K Kopt : Matrix n m ℝ) (S : Matrix m m ℝ)
    (hS : S.PosSemidef) (hopt : Kopt * S = B) :
    (posterior P B K S - posterior P B Kopt S).PosSemidef := by
  have hs : Sᵀ = S := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hS.1
  rw [gain_gap P B K Kopt S hs hopt]
  exact GNC.Estimation.CovariancePropagation.positive_semidefinite (K - Kopt) hS

theorem conditional_factor_identity (L : Matrix n n ℝ)
    (U K : Matrix n m ℝ) (V : Matrix m m ℝ) (H : Matrix m n ℝ) :
    let F := 1 - K * H
    let A := F * L - K * Uᵀ
    F * (L * Lᵀ) * Fᵀ + K * (Uᵀ * U + V * Vᵀ) * Kᵀ
      - F * (L * U) * Kᵀ - K * (L * U)ᵀ * Fᵀ =
      A * Aᵀ + (K * V) * (K * V)ᵀ := by
  dsimp only
  simp only [transpose_sub, transpose_mul, transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  abel

theorem conditional_factor_positive_semidefinite (L : Matrix n n ℝ)
    (U K : Matrix n m ℝ) (V : Matrix m m ℝ) (H : Matrix m n ℝ) :
    let F := 1 - K * H
    (F * (L * Lᵀ) * Fᵀ + K * (Uᵀ * U + V * Vᵀ) * Kᵀ
      - F * (L * U) * Kᵀ - K * (L * U)ᵀ * Fᵀ).PosSemidef := by
  dsimp only
  rw [conditional_factor_identity]
  exact (posSemidef_self_mul_conjTranspose (A := (1 - K * H) * L - K * Uᵀ)).add
    (posSemidef_self_mul_conjTranspose (A := K * V))

theorem impossible_scalar_joint :
    (1 : ℝ) > 0 ∧ (1 : ℝ) > 0 ∧ (1 : ℝ) + 2 * 2 + 1 > 0 ∧
      (1 : ℝ) - (1 + 2)^2 / (1 + 2 * 2 + 1) < 0 := by
  norm_num

end GNC.Estimation.KalmanCorrection
