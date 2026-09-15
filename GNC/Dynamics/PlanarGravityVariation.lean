import GNC.Dynamics.PolynomialOrbitTransition
import GNC.Dynamics.GravityLinearization

/-! Identify the polynomial transition coefficients with the derivative of
the physical inverse-square field. Gravity.field_derivative supplies the
calculus theorem; this module only proves its coordinate representation.
-/
noncomputable section
namespace GNC.PolynomialOrbitTransition
open Matrix

def position (w : Fin 4 → ℝ) : Vec3 := ![w 0,w 1,0]

theorem position_norm (w : Fin 4 → ℝ) : enorm (position w) = PolynomialOrbit.radius w := by
  have hs := enorm_sq (position w)
  simp [position, lengthSq, Matrix.cons_val_two] at hs
  change enorm (position w)^2 = w 0^2+w 1^2 at hs
  have hr := Real.sq_sqrt (show (0:ℝ) ≤ w 0^2+w 1^2 by positivity)
  unfold PolynomialOrbit.radius
  nlinarith [enorm_nonneg (position w), Real.sqrt_nonneg (w 0^2+w 1^2)]

def gravityMatrix (z : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3*z 4^5*z 0^2-z 4^3, 3*z 4^5*z 0*z 1, 0;
    3*z 4^5*z 0*z 1, 3*z 4^5*z 1^2-z 4^3, 0;
    0,0,-z 4^3]

/-- The matrix used by the transition integrator is the actual physical
gravity derivative, represented in the fixed Cartesian coordinates. -/
theorem gravity_matrix (w : Fin 4 → ℝ) (v : Vec3) :
    Gravity.gradient3 1 (position w) v = gravityMatrix (PolynomialOrbit.lift w) *ᵥ v := by
  change (3*1*inner ℝ (WithLp.toLp 2 (position w) : Jacobian.E3)
    (WithLp.toLp 2 v)/enorm (position w)^5) • position w -
      (1/enorm (position w)^3) • v = _
  rw [Gravity.inner_toLp, position_norm]
  funext i
  fin_cases i <;>
    simp [gravityMatrix, PolynomialOrbit.lift, position, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val_two, div_eq_mul_inv] <;> ring

/-- In-plane error kinematics plus the in-plane components of the physical
gravity derivative. Out-of-plane perturbations do not enter these rows. -/
theorem plane_action (w : Fin 4 → ℝ) (v : Fin 4 → ℝ) (normal : ℝ) :
    planeGenerator (PolynomialOrbit.lift w) *ᵥ v =
      ![v 2, v 3, (Gravity.gradient3 1 (position w) ![v 0,v 1,normal]) 0,
        (Gravity.gradient3 1 (position w) ![v 0,v 1,normal]) 1] := by
  rw [gravity_matrix]
  funext i
  fin_cases i <;>
    simp [planeGenerator, gravityMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

/-- The normal error equation is independent of in-plane displacement. -/
theorem normal_action (w : Fin 4 → ℝ) (v : Fin 2 → ℝ) (x y : ℝ) :
    normalGenerator (PolynomialOrbit.lift w) *ᵥ v =
      ![v 1, (Gravity.gradient3 1 (position w) ![x,y,v 0]) 2] := by
  rw [gravity_matrix]
  funext i
  fin_cases i <;>
    simp [normalGenerator, gravityMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two] <;> ring

end GNC.PolynomialOrbitTransition
