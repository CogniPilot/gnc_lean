import GNC.Lie.Adjoint

/-! Right Jacobian and inverse, identified with the actual matrix
differential, including zero attitude. -/
noncomputable section
open Matrix Real NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

@[simp] theorem hat_neg (x : LogState) : hat (-x) = -hat x := hatLinear.map_neg x

theorem blockLeft_neg (x y : LogState) : Jacobian.blockLeft x (-y) = -Jacobian.blockLeft x y := by
  have hz : Jacobian.blockLeft x 0 = 0 := by
    ext i j; fin_cases i <;> simp [Jacobian.blockLeft]
  have h := blockLeft_add x y (-y)
  rw [add_neg_cancel, hz] at h
  linear_combination (norm := module) -h

namespace Jacobian
def blockRight (x y : LogState) : LogState := blockLeft (-x) y
def blockRightInverse (x y : LogState) : LogState := blockInverse (-x) y

theorem blockRightInverse_right (x y : LogState) (hθ : enorm (x 2) < 2*π) :
    blockRightInverse x (blockRight x y) = y := by
  apply blockInverse_left_all
  simpa only [Pi.neg_apply, enorm_neg] using hθ

theorem blockRight_inverse (x y : LogState) (hθ : enorm (x 2) < 2*π) :
    blockRight x (blockRightInverse x y) = y := by
  apply blockLeft_inverse_all
  simpa only [Pi.neg_apply, enorm_neg] using hθ

theorem blockRightInverse_velocityOnly (x : LogState) (v : Vec3) :
    blockRightInverse x (velocityOnly v) = velocityOnly (inverseAt (-x 2) v) :=
  blockInverse_velocityOnly (-x) v
end Jacobian

/-- Equality of the left and right trivializations of the true differential. -/
theorem left_right_differential (x y : LogState) :
    hat (Jacobian.blockLeft x y)*exp (hat x) = exp (hat x)*hat (Jacobian.blockRight x y) := by
  have hp : HasDerivAt (fun s : ℝ => x+s • y) y 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const y).const_add x
  have hn := matrixExp_curve_derivative_all hp.neg
  have h := (matrixExp_affine_derivative_all x y).mul hn
  have he : (fun s : ℝ => exp (hat (x+s • y))*exp (hat (-(x+s • y)))) = fun _ => (1:Mat5) := by
    funext s
    rw [hat_neg, MixedInvariant.exp_cancel]
  change HasDerivAt (fun s : ℝ => exp (hat (x+s • y))*exp (hat (-(x+s • y)))) _ 0 at h
  rw [he] at h
  have hu := h.unique (hasDerivAt_const (0:ℝ) (1:Mat5))
  simp only [Pi.neg_apply, zero_smul, add_zero, blockLeft_neg, hat_neg, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc, MixedInvariant.exp_cancel, Matrix.mul_one] at hu
  have hb : hat (Jacobian.blockLeft x y) =
      exp (hat x)*(hat (Jacobian.blockLeft (-x) y)*exp (-hat x)) := by
    linear_combination (norm := module) hu
  have hc := congrArg (fun Z => Z*exp (hat x)) hb
  simpa only [Matrix.mul_assoc, MixedInvariant.exp_cancel', Matrix.mul_one] using hc

theorem matrixExp_right_derivative {x : ℝ → LogState} {y : LogState} {t : ℝ}
    (hx : HasDerivAt x y t) :
    HasDerivAt (fun s => exp (hat (x s)))
      (exp (hat (x t))*hat (Jacobian.blockRight (x t) y)) t := by
  simpa only [left_right_differential] using matrixExp_curve_derivative_all hx

theorem left_right_adjoint (x y : LogState) :
    Jacobian.blockLeft x y = adjoint (groupExp x) (Jacobian.blockRight x y) := by
  apply hat_injective
  have h := left_right_differential x y
  rw [← groupExp_toMatrix, ← hat_adjoint_intertwine] at h
  have hc := congrArg (fun Z => Z*SE23.toMatrix (groupExp x)⁻¹) h
  simpa only [Matrix.mul_assoc, matrix_mul_inv, Matrix.mul_one] using hc

/-- The transport identity used in the proof of Proposition 1. -/
theorem inverse_right_adjoint (x y : LogState) (hθ : enorm (x 2) < 2*π) :
    Jacobian.blockRightInverse x (adjoint (groupExp x)⁻¹ y) = Jacobian.blockInverse x y := by
  have h := left_right_adjoint x (Jacobian.blockInverse x y)
  rw [Jacobian.blockLeft_inverse_all _ _ hθ] at h
  have ha := congrArg (adjoint (groupExp x)⁻¹) h
  rw [adjoint_inv] at ha
  rw [ha, Jacobian.blockRightInverse_right _ _ hθ]

end GNC
