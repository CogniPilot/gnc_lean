import GNC.Dynamics.ForcedLogDynamics
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! The actual group adjoint and right-trivialized exponential differential. -/
noncomputable section
open Matrix Real NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem rotate_triple (R : SO3) (u v w : Vec3) :
    rotate R u ⬝ᵥ (rotate R v ⨯₃ rotate R w) = u ⬝ᵥ (v ⨯₃ w) := by
  rw [triple_product_eq_det, triple_product_eq_det]
  have he : ![rotate R u,rotate R v,rotate R w] =
      (Matrix.of ![u,v,w] * R.val.transpose : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> simp [rotate, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring
  have hd : R.val.det = 1 := R.property.2
  rw [he, det_mul, det_transpose, hd, mul_one]
  rfl

theorem rotate_cross (R : SO3) (u v : Vec3) :
    rotate R (u ⨯₃ v) = rotate R u ⨯₃ rotate R v := by
  have ht (z : Vec3) : rotate R z ⬝ᵥ
      (rotate R (u ⨯₃ v)-(rotate R u ⨯₃ rotate R v)) = 0 := by
    rw [dotProduct_sub, rotate_dot, rotate_triple, sub_self]
  apply sub_eq_zero.mp
  apply dotProduct_self_eq_zero.mp
  simpa only [← rotate_mul, mul_inv_cancel, rotate_one] using
    ht (rotate R⁻¹ (rotate R (u ⨯₃ v)-(rotate R u ⨯₃ rotate R v)))

theorem skew_rotate (R : SO3) (u : Vec3) : skew (rotate R u)*R.val = R.val*skew u := by
  apply Matrix.mulVec_injective
  funext v
  simp only [← mulVec_mulVec, skew_mulVec]
  exact (rotate_cross R u v).symm

/-- The coordinate group adjoint, including both translation columns. -/
def adjoint (X : SE23) (x : LogState) : LogState :=
  ![rotate X.rot (x 0)+X.pos ⨯₃ rotate X.rot (x 2),
    rotate X.rot (x 1)+X.vel ⨯₃ rotate X.rot (x 2), rotate X.rot (x 2)]

theorem hat_adjoint_intertwine (X : SE23) (x : LogState) :
    hat (adjoint X x)*SE23.toMatrix X = SE23.toMatrix X*hat x := by
  apply splitMatrix.injective
  simp only [map_mul, split_hat, split_group, Preintegration.block, fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero]
  simp only [adjoint, Matrix.cons_val]
  rw [skew_rotate]
  congr 1
  have ht (u v : Vec3) : skew (rotate X.rot (x 2)) *ᵥ u +
      (rotate X.rot v+u ⨯₃ rotate X.rot (x 2)) = rotate X.rot v := by
    rw [skew_mulVec, ← cross_anticomm (rotate X.rot (x 2)) u]
    module
  ext i j
  fin_cases j
  · exact congrFun (ht X.vel (x 1)) i
  · exact congrFun (ht X.pos (x 0)) i

/-- This is conjugation in the actual faithful matrix representation. -/
theorem hat_adjoint (X : SE23) (x : LogState) :
    hat (adjoint X x) = SE23.toMatrix X*hat x*SE23.toMatrix X⁻¹ := by
  rw [← hat_adjoint_intertwine, Matrix.mul_assoc, matrix_mul_inv, Matrix.mul_one]

theorem adjoint_mul (X Y : SE23) (x : LogState) : adjoint (X*Y) x = adjoint X (adjoint Y x) := by
  apply hat_injective
  simp only [hat_adjoint, SE23.toMatrix_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

@[simp] theorem adjoint_one (x : LogState) : adjoint 1 x = x := by
  ext i j; fin_cases i <;> simp [adjoint]

theorem adjoint_inv (X : SE23) (x : LogState) : adjoint X⁻¹ (adjoint X x) = x := by
  rw [← adjoint_mul, inv_mul_cancel, adjoint_one]

theorem adjoint_velocityOnly (X : SE23) (v : Vec3) :
    adjoint X (velocityOnly v) = velocityOnly (rotate X.rot v) := by
  ext i j; fin_cases i <;> simp [adjoint, velocityOnly]

end GNC
