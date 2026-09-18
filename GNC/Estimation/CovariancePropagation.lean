import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Covariance propagation with explicit moment hypotheses. Congruence is
exact for a linear map of random variables; using a flow Jacobian is a
linearization, not an exact nonlinear uncertainty theorem. -/
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace GNC.Estimation.CovariancePropagation
variable {m n k Ω : Type*} [Fintype m] [Fintype n] [Fintype k]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

def covarianceMatrix (X : Ω → n → ℝ) : Matrix n n ℝ :=
  fun i j => covariance (fun ω => X ω i) (fun ω => X ω j) μ

/-- No independence assumption is needed: off-diagonal initial covariance
is retained. This uses mathlib's covariance sum and scaling theorems. -/
theorem linear_pushforward (J : Matrix m n ℝ) (X : Ω → n → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    covarianceMatrix μ (fun ω => J *ᵥ X ω) = J * covarianceMatrix μ X * Jᵀ := by
  ext i j
  simp only [covarianceMatrix,Matrix.mulVec,dotProduct]
  rw [covariance_fun_sum_fun_sum (fun a => (hX a).const_mul (J i a))
    (fun a => (hX a).const_mul (J j a))]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [covarianceMatrix]
  ring

/-- Coordinate changes cannot improve physical first-order covariance when
the physical sensitivity is the same. -/
theorem coordinate_equivalence (C : Matrix m n ℝ) (L : Matrix n k ℝ)
    (P : Matrix k k ℝ) :
    C*(L*P*Lᵀ)*Cᵀ=(C*L)*P*(C*L)ᵀ := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem positive_semidefinite (J : Matrix m n ℝ) {P : Matrix n n ℝ}
    (hP : P.PosSemidef) : (J*P*Jᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.mul_mul_conjTranspose_same J

/-- A static uncertain parameter is part of the initial vector, and its
cross-covariances must be propagated through the same sensitivity map. -/
theorem same_sensitivity_same_covariance (J K : Matrix m n ℝ)
    (P : Matrix n n ℝ) (h : J=K) : J*P*Jᵀ=K*P*Kᵀ := by rw [h]

end GNC.Estimation.CovariancePropagation

namespace GNC.Estimation.CovariancePropagation
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A deterministic error certificate bounds the variance of the residual,
for any probability law supported on the certified set. -/
theorem residual_variance_bound {X Y : Ω → ℝ} {ε : ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (h : ∀ᵐ ω ∂μ, |X ω-Y ω|≤ε) :
    variance (fun ω => X ω-Y ω) μ≤ε^2 := by
  have hh := variance_le_sq_of_bounded
    (h.mono fun _ h => abs_le.mp h) (hX.sub hY)
  convert hh using 1 <;> ring

/-- A certified predictor can enclose the true directional variance without
assuming Gaussian errors or independence of the approximation residual.
The supplied predictor variance bound must itself be justified. -/
theorem variance_error_bound {X Y : Ω → ℝ} {ε σ : ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hε : 0<ε) (hσ : 0<σ)
    (h : ∀ᵐ ω ∂μ, |X ω-Y ω|≤ε) (hvar : variance Y μ≤σ^2) :
    |variance X μ-variance Y μ|≤2*σ*ε+ε^2 := by
  let e : Ω → ℝ := fun ω => X ω-Y ω
  have he : MemLp e 2 μ := hX.sub hY
  have hv : variance e μ≤ε^2 := residual_variance_bound μ hX.aemeasurable hY.aemeasurable h
  have hv0 := variance_nonneg e μ
  have hm := variance_nonneg (fun ω => ε*Y ω-σ*e ω) μ
  have hp := variance_nonneg (fun ω => ε*Y ω+σ*e ω) μ
  rw [variance_fun_sub (hY.const_mul ε) (he.const_mul σ)] at hm
  rw [variance_fun_add (hY.const_mul ε) (he.const_mul σ)] at hp
  simp only [variance_const_mul,covariance_const_mul_left,covariance_const_mul_right] at hm hp
  have hyb := mul_le_mul_of_nonneg_left hvar (sq_nonneg ε)
  have heb := mul_le_mul_of_nonneg_left hv (sq_nonneg σ)
  have hc : |covariance Y e μ|≤σ*ε := by
    apply abs_le.mpr
    constructor
    · refine le_of_mul_le_mul_left ?_ (show 0<2*ε*σ by positivity)
      nlinarith
    · refine le_of_mul_le_mul_left ?_ (show 0<2*ε*σ by positivity)
      nlinarith
  have hid : X=(fun ω => Y ω+e ω) := by funext ω; dsimp [e]; ring
  have hvx : variance X μ=variance Y μ+2*covariance Y e μ+variance e μ := by
    conv_lhs => rw [hid]
    exact variance_fun_add hY he
  rw [hvx]
  rcases abs_le.mp hc with ⟨hl,hu⟩
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg ε]

end GNC.Estimation.CovariancePropagation
