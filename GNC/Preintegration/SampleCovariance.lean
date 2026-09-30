import GNC.Estimation.CovariancePropagation
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Covariance of the first-variation preintegration model. Sample errors
are finite random vectors, not continuous white noise. Every covariance
identity below is exact for the specified linear random-variable map.
No exact nonlinear stochastic covariance claim is made.
-/
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open GNC.Estimation.CovariancePropagation
namespace GNC.Preintegration.Uncertainty
variable {n m Ω : Type*} [Fintype n] [Fintype m]

def jointMap (F : Matrix n n ℝ) (J₀ J₁ : Matrix n m ℝ) :
    Matrix n (n ⊕ (m ⊕ m)) ℝ := fromCols F (fromCols J₀ J₁)

theorem jointMap_apply (F : Matrix n n ℝ) (J₀ J₁ : Matrix n m ℝ)
    (e : n → ℝ) (n₀ n₁ : m → ℝ) :
    jointMap F J₀ J₁ *ᵥ Sum.elim e (Sum.elim n₀ n₁) =
      F *ᵥ e + (J₀ *ᵥ n₀ + J₁ *ᵥ n₁) := by
  simp [jointMap, fromCols_mulVec_sumElim]

theorem joint_sample_covariance [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Matrix n n ℝ) (J₀ J₁ : Matrix n m ℝ)
    (X : Ω → n ⊕ (m ⊕ m) → ℝ) (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    covarianceMatrix μ (fun ω => jointMap F J₀ J₁ *ᵥ X ω) =
      jointMap F J₀ J₁ * covarianceMatrix μ X * (jointMap F J₀ J₁)ᵀ :=
  linear_pushforward μ _ X hX

/-- All initial-state/input cross terms; independence is not implicit. -/
theorem correlated_update (F : Matrix n n ℝ) (J : Matrix n m ℝ)
    (P : Matrix n n ℝ) (C : Matrix n m ℝ) (Q : Matrix m m ℝ) :
    fromCols F J * fromBlocks P C Cᵀ Q * (fromCols F J)ᵀ =
      F*P*Fᵀ + J*Cᵀ*Fᵀ + F*C*Jᵀ + J*Q*Jᵀ := by
  rw [transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.add_mul]
  abel

theorem bias_map (J₀ J₁ : Matrix n m ℝ) (b : m → ℝ) :
    J₀ *ᵥ (-b) + J₁ *ᵥ (-b) = (-(J₀+J₁)) *ᵥ b := by
  simp [Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.add_mulVec, add_comm]

/-- If both endpoint perturbations are the same random variable, their
covariance is perfectly correlated; FOH reduces to the common-input map. -/
theorem equal_endpoint_covariance (J₀ J₁ : Matrix n m ℝ) (Q : Matrix m m ℝ) :
    fromCols J₀ J₁ * fromBlocks Q Q Q Q * (fromCols J₀ J₁)ᵀ =
      (J₀+J₁)*Q*(J₀+J₁)ᵀ := by
  rw [transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.transpose_add]

section Shared
variable [DecidableEq m]

/-- Retain the previous endpoint sample as part of the uncertainty state.
The bottom block is replaced by the next, fresh endpoint sample. -/
def retainedStep (F : Matrix n n ℝ) (J₀ : Matrix n m ℝ) : Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks F J₀ 0 0

def freshStep (J₁ : Matrix n m ℝ) : Matrix (n ⊕ m) m ℝ := fromRows J₁ 1

theorem shared_sample_state (F : Matrix n n ℝ) (J₀ J₁ : Matrix n m ℝ)
    (e : n → ℝ) (old fresh : m → ℝ) :
    retainedStep F J₀ *ᵥ Sum.elim e old + freshStep J₁ *ᵥ fresh =
      Sum.elim (F *ᵥ e + J₀ *ᵥ old + J₁ *ᵥ fresh) fresh := by
  ext i
  cases i <;> simp [retainedStep, freshStep, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, fromBlocks, fromRows, Matrix.one_apply]

/-- Exact covariance blocks when the fresh sample is uncorrelated with
the retained augmented state. `C` keeps the prior error/sample correlation.
The next correlation is `J₁ Qnext`, not zero. -/
theorem shared_sample_blocks (F : Matrix n n ℝ) (J₀ J₁ : Matrix n m ℝ)
    (P : Matrix n n ℝ) (C : Matrix n m ℝ) (Q Qnext : Matrix m m ℝ) :
    retainedStep F J₀ * fromBlocks P C Cᵀ Q * (retainedStep F J₀)ᵀ +
      freshStep J₁ * Qnext * (freshStep J₁)ᵀ =
    fromBlocks
      (F*P*Fᵀ + J₀*Cᵀ*Fᵀ + F*C*J₀ᵀ + J₀*Q*J₀ᵀ + J₁*Qnext*J₁ᵀ)
      (J₁*Qnext) (Qnext*J₁ᵀ) Qnext := by
  simp only [retainedStep, freshStep, fromBlocks_transpose, transpose_fromRows,
    fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    transpose_zero, transpose_one, fromRows_mul, fromRows_mul_fromCols, mul_fromCols,
    fromRows_fromCols_eq_fromBlocks, fromCols_fromRows_eq_fromBlocks,
    Matrix.mul_one, Matrix.one_mul, fromBlocks_add, Matrix.add_mul, add_assoc]

end Shared

/-- Positive semidefiniteness follows from the full joint covariance, even
with correlated endpoint samples and initial conditions. -/
theorem joint_sample_psd (F : Matrix n n ℝ) (J₀ J₁ : Matrix n m ℝ)
    {S : Matrix (n ⊕ (m ⊕ m)) (n ⊕ (m ⊕ m)) ℝ} (hS : S.PosSemidef) :
    (jointMap F J₀ J₁ * S * (jointMap F J₀ J₁)ᵀ).PosSemidef :=
  positive_semidefinite _ hS

end GNC.Preintegration.Uncertainty
