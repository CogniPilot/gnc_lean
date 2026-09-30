import GNC.Analysis.EuclideanOperatorFrobenius
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Orthonormal-column norm calculus for a posteriori physical flow bounds.
In particular, rotation transports a matrix defect without amplification. -/
noncomputable section
namespace GNC.EuclideanOperator

def columnsLinearMap (n : ℕ) : Operator n →ₗ[ℝ] PiLp 2 (fun _ : Fin n => Space n) where
  toFun := columns
  map_add' := by intro L K; ext j i; rfl
  map_smul' := by intro c L; ext j i; rfl

def columnsCLM (n : ℕ) : Operator n →L[ℝ] PiLp 2 (fun _ : Fin n => Space n) :=
  (columnsLinearMap n).mkContinuous (Real.sqrt n) (fun L => frobenius_le_operator L)

@[simp] theorem columnsCLM_apply {n : ℕ} (L : Operator n) : columnsCLM n L = columns L := rfl

@[simp] theorem frobenius_zero (n : ℕ) : frobenius (0 : Operator n) = 0 := by
  change ‖columnsCLM n 0‖ = 0
  simp only [map_zero, norm_zero]

@[simp] theorem frobenius_neg {n : ℕ} (L : Operator n) : frobenius (-L) = frobenius L := by
  change ‖columnsCLM n (-L)‖ = ‖columnsCLM n L‖
  rw [map_neg, norm_neg]

theorem star_entry {n : ℕ} (L : Operator n) (i j : Fin n) :
    star L (EuclideanSpace.single j 1) i = L (EuclideanSpace.single i 1) j := by
  have h := ContinuousLinearMap.adjoint_inner_right L (EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1)
  have hl := EuclideanSpace.inner_single_left (𝕜 := ℝ) i 1
    ((ContinuousLinearMap.adjoint L) (EuclideanSpace.single j 1))
  have hr := EuclideanSpace.inner_single_right (𝕜 := ℝ) j 1
    (L (EuclideanSpace.single i 1))
  simpa using hl.symm.trans (h.trans hr)

theorem frobenius_star {n : ℕ} (L : Operator n) : frobenius (star L) = frobenius L := by
  have hs : frobenius (star L)^2 = frobenius L^2 := by
    simp only [frobenius_sq, star_entry]
    exact Finset.sum_comm
  have h1 : 0 ≤ frobenius (star L) := norm_nonneg _
  have h2 : 0 ≤ frobenius L := norm_nonneg _
  nlinarith

theorem frobenius_mul_left {n : ℕ} (U L : Operator n)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : frobenius (U*L) = frobenius L := by
  have hs : frobenius (U*L)^2 = frobenius L^2 := by
    simp only [frobenius, PiLp.norm_sq_eq_of_L2, columns,
      ContinuousLinearMap.mul_apply, hU]
  have h1 : 0 ≤ frobenius (U*L) := norm_nonneg _
  have h2 : 0 ≤ frobenius L := norm_nonneg _
  nlinarith

theorem frobenius_mul_right {n : ℕ} (L U : Operator n)
    (hU : ∀ x, ‖star U x‖ = ‖x‖) : frobenius (L*U) = frobenius L := by
  rw [← frobenius_star (L*U), StarMul.star_mul L U, frobenius_mul_left _ _ hU,
    frobenius_star]

/-- Cauchy--Schwarz applied to the adjoint columns bounds the true Euclidean
action; the Frobenius certificate is also an operator-norm certificate. -/
theorem norm_apply_le_frobenius {n : ℕ} (L : Operator n) (x : Space n) :
    ‖L x‖ ≤ frobenius L * ‖x‖ := by
  have hi (i : Fin n) : |L x i| ≤ ‖star L (EuclideanSpace.single i 1)‖ * ‖x‖ := by
    have he : inner ℝ (star L (EuclideanSpace.single i 1)) x = L x i := by
      have h := ContinuousLinearMap.adjoint_inner_left L x (EuclideanSpace.single i 1)
      have hs := EuclideanSpace.inner_single_left (𝕜 := ℝ) i 1 (L x)
      simpa using h.trans hs
    rw [← he]
    exact abs_real_inner_le_norm _ _
  have hs : ‖L x‖^2 ≤ frobenius (star L)^2 * ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, frobenius, PiLp.norm_sq_eq_of_L2,
      Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hh := pow_le_pow_left₀ (abs_nonneg (L x i)) (hi i) 2
    simpa only [sq_abs, mul_pow, columns, PiLp.toLp_apply] using hh
  rw [frobenius_star] at hs
  have hn : 0 ≤ frobenius L * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith only [hs, hn, norm_nonneg (L x)]

end GNC.EuclideanOperator
