import GNC.Dynamics.GeometricSTMDefect
import GNC.Dynamics.GravityRemainderBall

/-! Shared reference-gradient responses with fixed pointing and magnitude error.
The identities keep the gravity gradient time dependent: they apply pointwise
along any supplied reference. They do not declare the nonlinear orbit log-linear.
Numerical reference/response defects remain explicit hypotheses in `bound`.
-/
noncomputable section
namespace GNC.ReferencePointingResponse
open Matrix Real

/-- A right-log linear perturbation reconstructed about the reference has
the physical form q + J(phi)y. This uses the actual SO(3) exponential. -/
theorem right_reconstruction (φ q y : Vec3) :
    rotate (rotationExp φ) q+
      Jacobian.leftAt φ (y-φ ⨯₃ q)=q+Jacobian.leftAt φ y := by
  rw [Jacobian.leftAt_sub,leftAt_cross_rotation]
  abel

def defect (μ ε : ℝ) (φ q y u qdd ydd : Vec3) : Vec3 :=
  Gravity.field3 μ (q+Jacobian.leftAt φ y)+(1+ε) • rotate (rotationExp φ) u-
    (qdd+Jacobian.leftAt φ ydd)

/-- Exact separation: reference defect, response defect, gradient/Jacobian
commutator, spatial gravity curvature, and angle/magnitude cross term. -/
theorem split (μ ε : ℝ) (φ q y u qdd ydd : Vec3) :
    defect μ ε φ q y u qdd ydd =
      (Gravity.field3 μ q+u-qdd)+
      Jacobian.leftAt φ (Gravity.gradient3 μ q y+φ ⨯₃ u+ε • u-ydd)+
      (Gravity.gradient3 μ q (Jacobian.leftAt φ y)-
        Jacobian.leftAt φ (Gravity.gradient3 μ q y))+
      Gravity.remainder3 μ q (Jacobian.leftAt φ y)+
      ε • (rotate (rotationExp φ) u-Jacobian.leftAt φ u) := by
  simp only [defect,Gravity.remainder3,Jacobian.leftAt_add,Jacobian.leftAt_sub,
    Jacobian.leftAt_smul,leftAt_cross_rotation]
  module

theorem magnitude_split (μ ε : ℝ) (φ q y u qdd ydd : Vec3) :
    defect μ ε φ q y u qdd ydd =
      GeometricSTMDefect.defect μ φ q y u qdd (ydd-ε • u)+
        ε • (rotate (rotationExp φ) u-Jacobian.leftAt φ u) := by
  simp only [defect,GeometricSTMDefect.defect,Jacobian.leftAt_sub,Jacobian.leftAt_smul]
  module

/-- Reuse the existing physical geometric-STM bound; the only additional
charge is the bounded magnitude/pointing cross term. C is an explicit input
bound, not a claim about an unchecked numerical rotation implementation. -/
theorem bound (μ : ℝ) (hμ : 0≤μ) (ε : ℝ) (φ q y u qdd ydd : Vec3)
    {r D εref εresponse C : ℝ} (hD : D<r) (hq : r≤enorm q)
    (hy : enorm y≤D) (hφ : enorm φ≤1)
    (href : enorm (Gravity.field3 μ q+u-qdd)≤εref)
    (hresponse : enorm (Gravity.gradient3 μ q y+φ ⨯₃ u+ε • u-ydd)≤εresponse)
    (hC : enorm (rotate (rotationExp φ) u-Jacobian.leftAt φ u)≤C) :
    enorm (defect μ ε φ q y u qdd ydd) ≤ εref+εresponse+
      2*(μ/enorm q^3)*enorm φ*enorm y+(4*μ/(r-D)^4)*enorm y^2+|ε| * C := by
  have hr : enorm (Gravity.gradient3 μ q y+φ ⨯₃ u-(ydd-ε • u))≤εresponse := by
    rw [show Gravity.gradient3 μ q y+φ ⨯₃ u-(ydd-ε • u)=
      Gravity.gradient3 μ q y+φ ⨯₃ u+ε • u-ydd by abel]
    exact hresponse
  have hb := GeometricSTMDefect.bound μ hμ φ q y u qdd (ydd-ε • u)
    hD hq hy hφ href hr
  rw [magnitude_split]
  apply (enorm_add_le _ _).trans
  apply add_le_add hb
  rw [enorm_smul]
  exact mul_le_mul_of_nonneg_left hC (abs_nonneg ε)

/-- Even a perfectly known fixed reference does not linearize the actual
inverse-square gravity error: its positive radial restriction fails homogeneity.
This is a statement about the actual field, not a polynomial stand-in. -/
theorem radial_gravity_error_not_linear :
    Gravity.field 1 (3:ℝ)-Gravity.field 1 (1:ℝ) ≠
      2*(Gravity.field 1 (2:ℝ)-Gravity.field 1 (1:ℝ)) := by
  norm_num [Gravity.field,Real.norm_eq_abs]

end GNC.ReferencePointingResponse
