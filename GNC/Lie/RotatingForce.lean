import GNC.Lie.AxisRotation

/-! Exact harmonic form of a fixed ambient matrix transported through a
planar reference rotation. The matrix may be a full three-dimensional attitude
offset, its infinitesimal generator, or another linear map. The input force
has arbitrary radial/transverse components. The phase need not be affine in
time. This is an algebraic identity, not a truncated time or angle series.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.RotatingForce
open Matrix Real
open scoped Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def harmonic (A : Mat3) (φ x y : ℝ) : Vec3 :=
  ![((A 0 0+A 1 1)/2+(A 0 0-A 1 1)/2*cos (2*φ)+
        (A 0 1+A 1 0)/2*sin (2*φ))*x+
      ((A 0 1-A 1 0)/2+(A 0 1+A 1 0)/2*cos (2*φ)+
        (A 1 1-A 0 0)/2*sin (2*φ))*y,
    ((A 1 0-A 0 1)/2+(A 0 1+A 1 0)/2*cos (2*φ)+
        (A 1 1-A 0 0)/2*sin (2*φ))*x+
      ((A 0 0+A 1 1)/2-(A 0 0-A 1 1)/2*cos (2*φ)-
        (A 0 1+A 1 0)/2*sin (2*φ))*y,
    (A 2 0*cos φ+A 2 1*sin φ)*x+(-A 2 0*sin φ+A 2 1*cos φ)*y]

theorem conjugation (A : Mat3) (φ x y : ℝ) :
    (AxisRotation.zMatrix (-φ)*A*AxisRotation.zMatrix φ) *ᵥ ![x,y,0]=
      harmonic A φ x y := by
  ext i
  fin_cases i <;>
    simp [harmonic,AxisRotation.zMatrix,Matrix.mulVec,Matrix.vecMul,Matrix.mul_apply,
      dotProduct,Fin.sum_univ_succ,cos_two_mul,sin_two_mul]
  · linear_combination (A 1 1*x-A 1 0*y)*(sin_sq_add_cos_sq φ)
  · linear_combination (-A 0 1*x+A 0 0*y)*(sin_sq_add_cos_sq φ)

/-- The reduction holds pointwise for any prescribed phase and force
histories; no constant-rate assumption is hidden in the harmonic notation. -/
theorem time_varying (A : Mat3) (φ x y : ℝ → ℝ) (t : ℝ) :
    (AxisRotation.zMatrix (-φ t)*A*AxisRotation.zMatrix (φ t)) *ᵥ ![x t,y t,0]=
      harmonic A (φ t) (x t) (y t) := conjugation A _ _ _

end GNC.RotatingForce
