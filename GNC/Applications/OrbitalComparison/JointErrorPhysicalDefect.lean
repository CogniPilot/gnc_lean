import GNC.Applications.OrbitalComparison.JointErrorData.Ranges
import GNC.Applications.OrbitalComparison.JointErrorData.Residual
import GNC.Applications.OrbitalComparison.JointErrorData.Constraint
import GNC.Applications.OrbitalComparison.JointErrorKinematics

/-! Complete pointwise defect of the actual three-axis candidate in full
inverse-square gravity. All coefficient, phase, scalar-radius and Jacobian
errors are included. Integrating this bound and proving physical existence
are separate from this pointwise theorem. -/
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial LieSTTOutput Set
noncomputable section

def referenceBudget (t : ℝ) : ℝ := (LieSTTData.Phase.harmonic1.error:ℝ)*t
def forceBudget (t : ℝ) : ℝ := (|radialForce t|+1/200000)*referenceBudget t
def radiusBudget (t : ℝ) : ℝ :=
  2*referenceBudget t*(1+JacobianPolynomial.tail (sigma:ℝ))*(rhoMaximum:ℝ)+
    2*(JacobianPolynomial.tail (sigma:ℝ)*(rhoMaximum:ℝ))+
    (JacobianPolynomial.tail (sigma:ℝ)*(rhoMaximum:ℝ))*
      (2*(rhoMaximum:ℝ)+JacobianPolynomial.tail (sigma:ℝ)*(rhoMaximum:ℝ))

def defectBudget (t : ℝ) : ℝ :=
  LieRadiusFullDefect.budget (modelInput.K:ℝ) 1 (sigma:ℝ)
    (rhoMaximum:ℝ) (offsetMaximum:ℝ) (referenceBudget t) (forceBudget t) (radiusBudget t)
    (PolynomialOrder.value constraintBound t) (PolynomialOrder.value residualBound t)

/-- Every attitude in the three-axis ball and every time in the burn is
covered. This is a bound on the full physical ODE, not a linearized field. -/
theorem physical_defect {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖acceleration x t-(Gravity.field (modelInput.K:ℝ) (position x t)+thrust x t)‖≤
      defectBudget t := by
  have hK : 0≤(modelInput.K:ℝ) := by exact_mod_cast model_K_nonnegative
  have hP : (rhoMaximum:ℝ)<1 := by
    have h0 : (0:ℝ)<rhoMaximum := by exact_mod_cast uniform_ranges_checked.2.2.1
    have h2 : 2*(rhoMaximum:ℝ)<1 := by exact_mod_cast uniform_ranges_checked.2.2.2.1
    linarith
  have hH : (offsetMaximum:ℝ)<1 := by exact_mod_cast uniform_ranges_checked.2.2.2.2.2
  have hf : enorm (exactForce t-value3 modelInput.force x t)≤forceBudget t := by
    simpa only [forceBudget,referenceBudget,mul_assoc] using force_error x ht
  have h := modelInput.physical_defect x t (exactReference t) (exactForce t)
    modelInput.cube hK (exactReference_norm t) (attitude_bound hx).2
    (attitude_bound hx).1 (rho_uniform hx ht) hP (offset_uniform hx ht) hH
    (reference_error x ht) hf (constraint_bound hx ht.1)
    (ε := 0) (by rw [modelInput.cube_value,sub_self,abs_zero]) (residual_bound hx ht.1)
  rw [physical_defect_value]
  simpa only [defectBudget,radiusBudget,referenceBudget,mul_zero,zero_mul,add_zero] using h

end
end GNC.OrbitalComparison.JointErrorData
