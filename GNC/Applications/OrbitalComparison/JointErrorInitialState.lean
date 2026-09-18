import GNC.Applications.OrbitalComparison.JointErrorKinematics
import GNC.Dynamics.LieGravityPullback

/-! Identify the stored candidate's initial state with the physical family
used in the experiment. The state is the arithmetic midpoint of the nominal
state and its finite rotation, not an independent position/velocity box.
The identities hold for every rotation vector, including zero. -/
noncomputable section
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial LieSTTOutput SpatialBurn Matrix

def initialReferencePosition : Vec3 := ![1,0,0]
def initialReferenceVelocity : Vec3 := ![0,3231/25000,0]

theorem rho_initial_value (x : Vec3) :
    value3 modelInput.rho x 0=(1/2:ℝ) • (x ⨯₃ initialReferencePosition) := by
  have hi (i : Fin 3) : value (rho i) x 0=value (initialPosition i) x 0 := by
    have h := ParameterPolynomial.identity _ _ (initial_position_checked i) x 0
    simpa only [value_atTime,Rat.cast_zero] using h
  change (fun i => value (rho i) x 0)=_
  ext i
  rw [hi]
  fin_cases i <;> norm_num [initialPosition,initialReferencePosition,crossProduct,
    value,termValue,monomial,PolynomialOrder.value,Planning.PolynomialKernel.evaluate,
    Matrix.cons_val_two,vecHead,vecTail] <;> ring

theorem rho_velocity_initial_value (x : Vec3) :
    value3 (PointingCapPolynomial.derivative modelInput.rho) x 0=
      (1/2:ℝ) • (x ⨯₃ initialReferenceVelocity) := by
  have hi (i : Fin 3) : value (ParameterPolynomial.derivative (rho i)) x 0=
      value (initialVelocity i) x 0 := by
    have h := ParameterPolynomial.identity _ _ (initial_velocity_checked i) x 0
    simpa only [value_atTime,Rat.cast_zero] using h
  change (fun i => value (ParameterPolynomial.derivative (rho i)) x 0)=_
  ext i
  rw [hi]
  fin_cases i <;> norm_num [initialVelocity,initialReferenceVelocity,crossProduct,
    value,termValue,monomial,PolynomialOrder.value,Planning.PolynomialKernel.evaluate,
    Matrix.cons_val_two,vecHead,vecTail] <;> ring

theorem reference_initial_position : exactReference 0=initialReferencePosition := by
  simp [exactReference,phase,initialReferencePosition]

theorem reference_initial_velocity : (referenceVelocity 0).ofLp=initialReferenceVelocity := by
  norm_num [referenceVelocity,VaryingRateReference.velocity,SpatialRotatingFrame.mix,
    pack_eq,phase,referenceRate,PolynomialOrder.value,Planning.PolynomialKernel.evaluate,
    initialReferenceVelocity]

theorem initial_position_midpoint (x : Vec3) :
    (position x 0).ofLp=(1/2:ℝ) •
      (initialReferencePosition+rotate (rotationExp x) initialReferencePosition) := by
  rw [position_value,rho_initial_value,reference_initial_position,
    Jacobian.leftAt_smul,leftAt_cross_rotation]
  module

theorem initial_velocity_midpoint (x : Vec3) :
    (velocity x 0).ofLp=(1/2:ℝ) •
      (initialReferenceVelocity+rotate (rotationExp x) initialReferenceVelocity) := by
  have hv (p : PointingCapPolynomial.Vector) :
      (PointingCapPolynomial.vectorValue p x 0).ofLp=value3 p x 0 := by
    ext i
    fin_cases i <;> simp [PointingCapPolynomial.vectorValue,value3,pack_eq]
  change (referenceVelocity 0).ofLp+Jacobian.leftAt x
    (PointingCapPolynomial.vectorValue (PointingCapPolynomial.derivative modelInput.rho) x 0).ofLp=_
  rw [hv,rho_velocity_initial_value,reference_initial_velocity,
    Jacobian.leftAt_smul,leftAt_cross_rotation]
  module

end GNC.OrbitalComparison.JointErrorData
