import GNC.Applications.OrbitalComparison.JointErrorPhysicalDefect
import GNC.Dynamics.PolynomialForcingCertificate

/-! Rational time profile for the complete three-axis physical defect.
Every coefficient is derived from the checked residual, inverse-radius
constraint and reference phase. No numerical allowance is supplied. -/
namespace GNC.OrbitalComparison.JointErrorData
open Planning.PolynomialKernel

def phaseBudget : ℚ := LieSTTData.Phase.harmonic1.error
def radialCoefficients : List ℚ :=
  [modelInput.K-(3231/25000)^2,-2*(3231/25000)*(1/200000),-(1/200000)^2]
def forceMagnitudeBound : ℚ := PolynomialBounds.bound radialCoefficients 1+1/200000
def jacobianTail : ℚ := sigma^9/3628800+sigma^10/39916800
def inverseResidual : ℚ := sigma^4/720+sigma^5/1440+sigma^6/5040+
  sigma^7/24192+sigma^8/241920+sigma^9/483840+
  (sigma^8/362880+sigma^9/3628800)*(1+sigma/2+sigma^2/12)
def cubeVariation : ℚ := 3*offsetMaximum+3*offsetMaximum^2+offsetMaximum^3
def radiusConstant : ℚ := 2*jacobianTail*rhoMaximum+
  (jacobianTail*rhoMaximum)*(2*rhoMaximum+jacobianTail*rhoMaximum)
def radiusLinear : ℚ := 2*phaseBudget*(1+jacobianTail)*rhoMaximum
def normalizedRadiusUpper : ℚ := (1+rhoMaximum)*(1+offsetMaximum)
def gravityFactor : ℚ := modelInput.K/(1-rhoMaximum)^2*
  (normalizedRadiusUpper^2+normalizedRadiusUpper+1)/(normalizedRadiusUpper+1)
def exactGain : ℚ := 2*modelInput.K/(1-2*rhoMaximum)^3
def lowForcing : List ℚ :=
  [modelInput.K*cubeVariation*inverseResidual+
      gravityFactor*radiusConstant*(1+offsetMaximum)^2,
    sigma*forceMagnitudeBound*phaseBudget+
      modelInput.K*cubeVariation*(1+sigma/2+sigma^2/12)*phaseBudget+
      gravityFactor*radiusLinear*(1+offsetMaximum)^2]
def rawForcing : List ℚ := PolynomialBounds.add residualBound
  (PolynomialBounds.add (PolynomialBounds.scale gravityFactor constraintBound) lowForcing)

noncomputable section
open Set

theorem radialCoefficients_value (t : ℝ) :
    PolynomialOrder.value radialCoefficients t=radialForce t := by
  simp only [radialCoefficients,radialForce,referenceRate,PolynomialOrder.value,
    List.map_cons,List.map_nil,evaluate,Rat.coe_castHom,Rat.cast_sub,Rat.cast_neg,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

theorem force_magnitude_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |radialForce t|+1/200000≤(forceMagnitudeBound:ℝ) := by
  have h := PolynomialBounds.bound_sound radialCoefficients
    (h := 1) (show |t|≤((1:ℚ):ℝ) by simpa only [abs_of_nonneg ht.1,Rat.cast_one] using ht.2)
  change |PolynomialOrder.value radialCoefficients t|≤_ at h
  rw [radialCoefficients_value] at h
  simpa only [forceMagnitudeBound,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    using add_le_add_left h (1/200000:ℝ)

theorem rawForcing_value (t : ℝ) : PolynomialOrder.value rawForcing t=
    LieRadiusFullDefect.budget (modelInput.K:ℝ) 1 (sigma:ℝ)
      (rhoMaximum:ℝ) (offsetMaximum:ℝ) (referenceBudget t)
      ((forceMagnitudeBound:ℝ)*referenceBudget t) (radiusBudget t)
      (PolynomialOrder.value constraintBound t) (PolynomialOrder.value residualBound t) := by
  simp only [rawForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale]
  simp only [lowForcing,PolynomialOrder.value,List.map_cons,List.map_nil,evaluate,
    Rat.coe_castHom,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  simp only [LieRadiusFullDefect.budget,referenceBudget,radiusBudget,
    phaseBudget,cubeVariation,inverseResidual,gravityFactor,normalizedRadiusUpper,
    radiusConstant,radiusLinear,jacobianTail,JacobianPolynomial.tail,
    inverseQuadraticBudget,Gravity.inverseRadiusFactor,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

/-- The time-dependent residual remains a polynomial profile, rather than
being replaced by its largest value over the burn. -/
theorem defectBudget_le_rawForcing {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    defectBudget t≤PolynomialOrder.value rawForcing t := by
  have hδ : 0≤(phaseBudget:ℝ) := by norm_num [phaseBudget,LieSTTData.Phase.harmonic1]
  have hq : 0≤referenceBudget t := mul_nonneg hδ ht.1
  have hf : forceBudget t≤(forceMagnitudeBound:ℝ)*referenceBudget t :=
    mul_le_mul_of_nonneg_right (force_magnitude_bound ht) hq
  have hσ : 0≤(sigma:ℝ) := by norm_num [sigma]
  rw [rawForcing_value]
  simp only [defectBudget,LieRadiusFullDefect.budget]
  gcongr

theorem physical_defect_profile {x : Vec3} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤(sigma:ℝ)^2) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖acceleration x t-(Gravity.field (modelInput.K:ℝ) (position x t)+thrust x t)‖≤
      PolynomialOrder.value rawForcing t :=
  (physical_defect hx ht).trans (defectBudget_le_rawForcing ht)

end
end GNC.OrbitalComparison.JointErrorData
