import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! Exact noise-factor transformations for comparing estimation coordinates.
The covariance congruence is proved algebraically for a supplied noise factor;
no stochastic independence or distribution assumptions are fabricated. -/
noncomputable section
open Matrix
namespace GNC.Estimation
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

theorem noise_factor_congruence (T : Matrix m n ℝ) (L : Matrix n k ℝ) :
    (T*L)*(T*L)ᵀ = T*(L*Lᵀ)*Tᵀ := by
  rw [transpose_mul]
  simp only [Matrix.mul_assoc]

theorem scaled_isotropic_noise [DecidableEq n] (R : Matrix n n ℝ)
    (hR : Rᵀ*R = 1) (s q : ℝ) :
    (s⁻¹ • Rᵀ)*(q • (1 : Matrix n n ℝ))*(s⁻¹ • Rᵀ)ᵀ =
      (q/s^2) • (1 : Matrix n n ℝ) := by
  simp only [transpose_smul, transpose_transpose, smul_mul_smul_comm,
    Matrix.mul_one, hR, smul_smul]
  congr 1
  ring

/-- Nonzero physical scale s=2 reduces isotropic measurement variance by
four in the invariant residual. Reusing the same scalar is not equivalent. -/
theorem scale_two_noise : (1 : ℝ)/(2:ℝ)^2 = 1/4 := by norm_num

end GNC.Estimation
