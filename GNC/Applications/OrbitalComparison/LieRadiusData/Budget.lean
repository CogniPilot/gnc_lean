import GNC.Applications.OrbitalComparison.LieRadiusData
import GNC.Applications.OrbitalComparison.LieRadiusCertification
import GNC.Applications.OrbitalComparison.LieSTTData.Lie3

/-! Exact rational budgets derived from the checked direct range records.
Known reference-phase and forcing checks are reused from the same physical
model. This file constructs no Cartesian trajectory witness.
-/
namespace GNC.OrbitalComparison.LieRadiusData
open Planning.PolynomialKernel

def sigma : ℚ := 7/20
def Zmax : ℚ := evaluate (z.bound 0) 1
def Hmax : ℚ := evaluate (h.bound 0) 1
def Umax : ℚ := evaluate (u.bound 0) 1
def delta : ℚ := LieSTTOutput.axisError LieSTTData.Lie3.record
def Ctheta : ℚ := LieSTTOutput.cosineBound LieSTTData.Lie3.record
def Htheta : ℚ := LieSTTOutput.sineBound LieSTTData.Lie3.record
def forceBound : ℚ := LieSTTData.Lie3.record.forceBound
def translationTail : ℚ := sigma^9/362880+sigma^10/3628800+
  Ctheta*delta+Htheta*delta*(2+delta)
def gramTail : ℚ := 2*sigma^10/3628800+(sigma^2+2*Ctheta)*delta*(2+delta)
def radiusError : ℚ := (2/input.r)*translationTail*Zmax+gramTail*Zmax^2/input.r^2
def regionRadius : ℚ := sigma*Zmax
def inverseBound : ℚ := (1+sigma/2+sigma^2/12)*input.r
def inverseAxisError : ℚ := (sigma/2+sigma^2*(2+delta)/12)*delta*input.r
def inverseResidual : ℚ := input.r*(sigma^4/720+sigma^5/1440+sigma^6/5040+
  sigma^7/24192+sigma^8/241920+sigma^9/483840+
  (sigma^8/362880+sigma^9/3628800)*(1+sigma/2+sigma^2/12))
def normalizedRadiusUpper : ℚ := (input.r+regionRadius)*(1+Hmax)/input.r
def gravityFactor : ℚ := input.μ/(input.r-regionRadius)^2*
  (normalizedRadiusUpper^2+normalizedRadiusUpper+1)/(normalizedRadiusUpper+1)
def exactGain : ℚ := 2*input.μ/(input.r-2*regionRadius)^3
def lowForcing : List ℚ :=
  [sigma*delta*forceBound,0,
    3*input.K*Hmax*inverseAxisError+3*input.K*Hmax*inverseResidual+gravityFactor*radiusError,0,
    3*input.K*Hmax^2*(regionRadius+inverseBound)+3*input.K*Hmax^2*inverseResidual+
      gravityFactor*(Hmax^2+2*(Umax+radiusError)*Hmax),0,
    input.K*Hmax^3*(regionRadius+inverseBound)+input.K*Hmax^3*inverseResidual+
      gravityFactor*(Umax+radiusError)*Hmax^2]
def rawForcing : List ℚ := PolynomialBounds.add (lie_residual.bound 0)
  (PolynomialBounds.add (PolynomialBounds.scale gravityFactor (constraint_linear.bound 0)) lowForcing)

theorem basic_checks : 0 ≤ input.μ ∧ 0 < input.r ∧ 0≤sigma ∧
    0≤Zmax ∧ 0≤Hmax ∧ Hmax<1 ∧ 0≤Umax ∧ 0≤delta ∧
    0≤Ctheta ∧ 0≤Htheta ∧ 0≤forceBound ∧ 0≤radiusError ∧
    0<regionRadius ∧ 2*regionRadius < input.r := by decide +kernel

theorem residual_nonnegative : PolynomialOrder.nonnegative (lie_residual.bound 0) := by decide +kernel
theorem constraint_nonnegative : PolynomialOrder.nonnegative (constraint_linear.bound 0) := by decide +kernel

noncomputable section
open LieRadiusPolynomial ParameterPolynomial PointingCapPolynomial SpatialBurn Matrix Set

theorem model_eq : input.model=LieSTTData.Lie3.record.model := rfl
theorem axis_polynomial_eq : input.axis=LieSTTOutput.axisPolynomial LieSTTData.Lie3.record := rfl

theorem axis_bound {θ t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (LieSTTOutput.axis (input.model.phase t)-LieSTTOutput.value3 input.axis ![θ,0,0] t)≤
      (delta:ℝ) := by
  rw [model_eq,axis_polynomial_eq]
  exact LieSTTOutput.axis_error LieSTTData.Lie3.record LieSTTData.Lie3.valid ht

theorem force_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm ![input.model.radial t,input.model.tangent,0]≤(forceBound:ℝ) := by
  have hn := pack_norm_le (input.model.radial t) input.model.tangent 0
  rw [pack_eq] at hn
  change enorm _≤_ at hn
  simp only [abs_zero,add_zero] at hn
  exact hn.trans (by rw [model_eq]; exact LieSTTData.Lie3.record.force_bound ht)

theorem cosine_bound {θ t : ℝ} (hθ : |θ|≤(sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    |OcticPointing.cosineLoss θ|≤(Ctheta:ℝ) := by
  simpa only [VaryingRatePolynomial.cosine_octic] using
    ParameterPolynomial.bound_sound (VaryingRatePolynomial.cosineLoss .octic)
      (VaryingRatePolynomial.parameter_bound .octic hθ) ht

theorem sine_bound {θ t : ℝ} (hθ : |θ|≤(sigma:ℝ)) (ht : t ∈ Icc (0:ℝ) 1) :
    |θ-OcticPointing.sine θ|≤(Htheta:ℝ) := by
  have hx : VaryingRatePolynomial.parameter .octic θ 0=θ := rfl
  simpa only [value_subtract,value_u,hx,VaryingRatePolynomial.sine_octic] using
    ParameterPolynomial.bound_sound (subtract PointingCapPolynomial.u (VaryingRatePolynomial.sine .octic))
      (VaryingRatePolynomial.parameter_bound .octic hθ) ht

theorem rawForcing_value (t : ℝ) : PolynomialOrder.value rawForcing t=
    LieRadiusTimeBound.forcing (input.μ:ℝ) (input.r:ℝ) (sigma:ℝ) (delta:ℝ)
      (regionRadius:ℝ) (Hmax:ℝ) (Umax:ℝ) (radiusError:ℝ) (forceBound:ℝ) t
      (PolynomialOrder.value (lie_residual.bound 0) t)
      (PolynomialOrder.value (constraint_linear.bound 0) t) := by
  simp only [rawForcing,PolynomialOrder.value_add,PolynomialOrder.value_scale]
  simp only [lowForcing,PolynomialOrder.value,Planning.PolynomialKernel.evaluate,
    List.map_cons,List.map_nil,Rat.coe_castHom,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_zero]
  simp only [LieRadiusTimeBound.forcing,LieRadiusPolynomial.Input.K,inverseBound,inverseAxisError,
    inverseResidual,gravityFactor,normalizedRadiusUpper,inverseQuadraticBudget,Gravity.inverseRadiusFactor,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
  ring

end
end GNC.OrbitalComparison.LieRadiusData
