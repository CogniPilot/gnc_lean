import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Model
import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Defect

/-! The delivered rank-two position and velocity queries, including their
actual derivatives and their exact common initial physical state. The
velocity delivered by the tensor fit is charged separately from the
derivative of the fitted position. -/
noncomputable section
namespace GNC.OrbitalComparison.TDSTTData.Lie2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput SpatialBurn

theorem polynomial_value (p : PointingCapPolynomial.Vector) (x : Vec3) (t : ℝ) :
    PointingCapPolynomial.vectorValue p x t=WithLp.toLp 2 (value3 p x t) := by
  ext i
  fin_cases i <;> simp [PointingCapPolynomial.vectorValue,value3,pack_eq]

def candidatePosition (x : Vec3) (t : ℝ) : E3 :=
  WithLp.toLp 2 (JointErrorData.exactReference t)+LieRadiusFrame.left x (PointingCapPolynomial.vectorValue position x t)
def candidateVelocity (x : Vec3) (t : ℝ) : E3 :=
  JointErrorData.referenceVelocity t+
    LieRadiusFrame.left x (PointingCapPolynomial.vectorValue (PointingCapPolynomial.derivative position) x t)
def deliveredVelocity (x : Vec3) (t : ℝ) : E3 :=
  JointErrorData.referenceVelocity t+LieRadiusFrame.left x (PointingCapPolynomial.vectorValue velocity x t)
def candidateAcceleration (x : Vec3) (t : ℝ) : E3 :=
  Gravity.field (physicalInput.K:ℝ) (WithLp.toLp 2 (JointErrorData.exactReference t))+
    WithLp.toLp 2 (JointErrorData.exactForce t)+
    LieRadiusFrame.left x (PointingCapPolynomial.vectorValue (PointingCapPolynomial.derivative
      (PointingCapPolynomial.derivative position)) x t)
def thrust (x : Vec3) (t : ℝ) : E3 :=
  WithLp.toLp 2 (rotate (rotationExp x) (JointErrorData.exactForce t))

theorem position_derivative (x : Vec3) (t : ℝ) :
    HasDerivAt (candidatePosition x) (candidateVelocity x t) t :=
  (JointErrorData.reference_position_derivative t).add (LieRadiusFrame.left_derivative x (PointingCapPolynomial.vector_derivative _ _ _))
theorem velocity_derivative (x : Vec3) (t : ℝ) :
    HasDerivAt (candidateVelocity x) (candidateAcceleration x t) t :=
  (JointErrorData.reference_velocity_derivative t).add (LieRadiusFrame.left_derivative x (PointingCapPolynomial.vector_derivative _ _ _))

theorem position_initial (x : Vec3) :
    candidatePosition x 0=WithLp.toLp 2 (JointErrorData.exactReference 0) := by
  have hi : PointingCapPolynomial.vectorValue position x 0=0 := by
    rw [polynomial_value]
    ext i
    have h := ParameterPolynomial.value_zero _ (initial_position_checked i) x 0
    simpa only [value_atTime,Rat.cast_zero] using h
  simp only [candidatePosition,hi,map_zero,add_zero]

theorem velocity_initial (x : Vec3) : candidateVelocity x 0=JointErrorData.referenceVelocity 0 := by
  have hi : PointingCapPolynomial.vectorValue (PointingCapPolynomial.derivative position) x 0=0 := by
    rw [polynomial_value]
    ext i
    have h := ParameterPolynomial.value_zero _ (initial_derivative_checked i) x 0
    simpa only [value_atTime,Rat.cast_zero] using h
  simp only [candidateVelocity,hi,map_zero,add_zero]

theorem delivered_initial (x : Vec3) : deliveredVelocity x 0=JointErrorData.referenceVelocity 0 := by
  have hi : PointingCapPolynomial.vectorValue velocity x 0=0 := by
    rw [polynomial_value]
    ext i
    have h := ParameterPolynomial.value_zero _ (initial_velocity_checked i) x 0
    simpa only [value_atTime,Rat.cast_zero] using h
  simp only [deliveredVelocity,hi,map_zero,add_zero]

theorem kinematic_value (x : Vec3) (t : ℝ) :
    candidateVelocity x t-deliveredVelocity x t=
      LieRadiusFrame.left x (PointingCapPolynomial.vectorValue kinematicCore x t) := by
  have hc (i : Fin 3) := ParameterPolynomial.identity _ _ (kinematic_checked i) x t
  simp only [kinematic,value_subtract] at hc
  simp only [candidateVelocity,deliveredVelocity,add_sub_add_left_eq_sub,←map_sub]
  congr 1
  simp only [polynomial_value]
  ext i
  exact hc i

theorem delivered_velocity_discrepancy {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤((1/10:ℚ):ℝ)^2) (ht : 0≤t) :
    ‖candidateVelocity x t-deliveredVelocity x t‖≤
      PolynomialOrder.value (kinematicRange.bound 1) t := by
  rw [kinematic_value]
  apply (LieRadiusFrame.left_norm x (attitude_bound hx).2 _).trans
  rw [polynomial_value]
  exact kinematic_range_bound hx ht

theorem physical_defect_value (x : Vec3) (t : ℝ) :
    ‖candidateAcceleration x t-(Gravity.field (physicalInput.K:ℝ) (candidatePosition x t)+thrust x t)‖=
      enorm (Gravity.field3 (physicalInput.K:ℝ) (JointErrorData.exactReference t)+
        JointErrorData.exactForce t+
        Jacobian.leftAt x (value3 (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative physicalInput.rho)) x t)-
        (Gravity.field3 (physicalInput.K:ℝ) (JointErrorData.exactReference t+Jacobian.leftAt x (value3 physicalInput.rho x t))+
          rotate (rotationExp x) (JointErrorData.exactForce t))) := by
  simp only [candidateAcceleration,candidatePosition,thrust,LieRadiusFrame.left,polynomial_value]
  rfl

end GNC.OrbitalComparison.TDSTTData.Lie2
