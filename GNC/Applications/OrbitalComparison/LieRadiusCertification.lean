import GNC.Applications.OrbitalComparison.LieRadiusModel
import GNC.Dynamics.LieRadiusTimeBound
import GNC.Dynamics.PolynomialForcingCertificate

/-! Compose direct Lie polynomial checks with the actual inertial orbit
candidate. No Cartesian polynomial trajectory witness is used by this path.
-/
noncomputable section
namespace GNC.OrbitalComparison.LieRadiusPolynomial
open SpatialBurn VaryingRateBurn VaryingRateFrame Matrix ParameterPolynomial
open LieSTTOutput LieRadiusDefect

theorem Input.translation_value3 (D : Input) (θ t : ℝ) :
    (D.translation θ t).ofLp=value3 D.rho ![θ,0,0] t := by
  ext i
  fin_cases i <;> simp [Input.translation,PointingCapPolynomial.vectorValue,value3,pack_eq]

theorem Input.body_radius (D : Input) (θ t : ℝ) :
    ‖D.position θ t‖=enorm (![(D.r:ℝ),0,0]+
      Jacobian.leftAt (θ • LieSTTOutput.axis (D.model.phase t)) (D.translation θ t).ofLp) := by
  rw [Input.position,LieRadiusFrame.position_body,LieRadiusFrame.reference_body,←map_add,turn_norm,
    pack_eq]
  rfl

/-- The stored polynomial norm bounds the precise residual used in the
direct full-gravity theorem. Scalar multiplication by the reference radius
is exact and carries no approximate inverse assumption. -/
theorem Input.checked_residual (D : Input) (θ t : ℝ) :
    value3 D.residual ![θ,0,0] t=
      (LieRadiusFrame.covariantAcceleration D.model (D.translation θ)
        (D.translationVelocity θ) (D.translationAcceleration θ) t).ofLp+
      ((D.μ:ℝ)/(D.r:ℝ)^3) • (D.translation θ t).ofLp+
      (3*((D.μ:ℝ)/(D.r:ℝ)^3)*value D.h ![θ,0,0] t) • (D.translation θ t).ofLp-
      (θ • value3 D.axis ![θ,0,0] t) ⨯₃ ![D.model.radial t,D.model.tangent,0]+
      (3*((D.μ:ℝ)/(D.r:ℝ)^3)*value D.h ![θ,0,0] t) •
        jacobianInverseQuadratic (θ • value3 D.axis ![θ,0,0] t) ![(D.r:ℝ),0,0] := by
  have he : (![(D.r:ℝ),0,0] : Vec3)=(D.r:ℝ) • ![1,0,0] := by
    ext i
    fin_cases i <;> simp
  have hp (φ : Vec3) : jacobianInverseQuadratic φ ![(D.r:ℝ),0,0]=
      (D.r:ℝ) • jacobianInverseQuadratic φ ![1,0,0] := by
    rw [he]
    simp only [jacobianInverseQuadratic,map_smul,LinearMap.smul_apply]
    module
  rw [D.residual_value,D.translation_value3,hp]
  simp only [Input.K,Rat.cast_div,Rat.cast_pow]
  module

theorem Input.physical_defect_expression (D : Input) (hr : 0<(D.r:ℝ)) (θ t : ℝ) :
    ‖D.acceleration θ t-D.model.acceleration θ t (D.position θ t)‖=
      enorm (Gravity.field3 D.model.μ ![D.model.r,0,0]+![D.model.radial t,D.model.tangent,0]+
        Jacobian.leftAt (θ • LieSTTOutput.axis (D.model.phase t))
          (LieRadiusFrame.covariantAcceleration D.model (D.translation θ)
            (D.translationVelocity θ) (D.translationAcceleration θ) t).ofLp-
        (Gravity.field3 D.model.μ (![D.model.r,0,0]+
          Jacobian.leftAt (θ • LieSTTOutput.axis (D.model.phase t)) (D.translation θ t).ofLp)+
          rotate (rotationExp (θ • LieSTTOutput.axis (D.model.phase t))) ![D.model.radial t,D.model.tangent,0])) := by
  have hs : ![D.model.radial t,D.model.tangent,0]+(D.model.source θ t).ofLp=
      rotate (rotationExp (θ • LieSTTOutput.axis (D.model.phase t))) ![D.model.radial t,D.model.tangent,0] := by
    change ![D.model.radial t,D.model.tangent,0]+(VaryingRateForcing.source θ (D.model.phase t)
      (D.model.radial t) D.model.tangent).ofLp=_
    rw [LieRadiusFrame.source_left]
    change ![D.model.radial t,D.model.tangent,0]+
      Jacobian.leftAt (θ • LieSTTOutput.axis (D.model.phase t))
        ((θ • LieSTTOutput.axis (D.model.phase t)) ⨯₃ ![D.model.radial t,D.model.tangent,0])=_
    rw [leftAt_cross_rotation]
    module
  rw [Input.acceleration,Input.position,LieRadiusFrame.physical_defect_norm D.model hr]
  simp only [pack_eq]
  change enorm (Gravity.field3 D.model.μ ![D.model.r,0,0]+![D.model.radial t,D.model.tangent,0]+
    Jacobian.leftAt (θ • LieSTTOutput.axis (D.model.phase t))
      (LieRadiusFrame.covariantAcceleration D.model (D.translation θ)
        (D.translationVelocity θ) (D.translationAcceleration θ) t).ofLp-
    (Gravity.field3 D.model.μ (![D.model.r,0,0]+
      Jacobian.leftAt (θ • LieSTTOutput.axis (D.model.phase t)) (D.translation θ t).ofLp)+
      (![D.model.radial t,D.model.tangent,0]+(D.model.source θ t).ofLp)))=_
  rw [hs]

/-- Direct range hypotheses on the stored polynomial and its scalar radius
approximation imply the actual physical acceleration defect bound. -/
theorem Input.direct_defect (D : Input) (hμ : 0≤(D.μ:ℝ)) (hr : 0<(D.r:ℝ))
    (θ t : ℝ) (hθ : |θ|<2*Real.pi) {δ P H U E C R B : ℝ}
    (hδ : enorm (LieSTTOutput.axis (D.model.phase t)-value3 D.axis ![θ,0,0] t)≤δ)
    (hρ : ‖D.translation θ t‖≤P) (hP : P<(D.r:ℝ))
    (hh : |value D.h ![θ,0,0] t|≤H) (hH : H<1)
    (hb : enorm ![D.model.radial t,D.model.tangent,0]≤B)
    (hs : |value D.radiusDeviation ![θ,0,0] t|≤U)
    (he : |(‖D.position θ t‖^2/(D.r:ℝ)^2-1)-value D.radiusDeviation ![θ,0,0] t|≤E)
    (hc : |value D.constraintLinear ![θ,0,0] t|≤C)
    (hR : enorm (value3 D.residual ![θ,0,0] t)≤R) :
    ‖D.acceleration θ t-D.model.acceleration θ t (D.position θ t)‖≤
      budget (D.μ:ℝ) (D.r:ℝ) θ δ P H U E C R B := by
  have hq : enorm (![(D.r:ℝ),0,0] : Vec3)=(D.r:ℝ) := by
    have hn := enorm_sq (![(D.r:ℝ),0,0] : Vec3)
    change enorm (![(D.r:ℝ),0,0] : Vec3)^2=(D.r:ℝ)^2+0^2+0^2 at hn
    norm_num only [zero_pow,add_zero] at hn
    nlinarith [enorm_nonneg (![(D.r:ℝ),0,0] : Vec3)]
  have hφ : enorm (θ • LieSTTOutput.axis (D.model.phase t))<2*Real.pi := by
    simpa only [enorm_smul,Gravity.unit_enorm _ (axis_unit _),mul_one] using hθ
  rw [Input.constraintLinear,value_add,value_scale] at hc
  norm_num only [Rat.cast_ofNat] at hc
  rw [D.body_radius] at he
  rw [D.checked_residual] at hR
  have Hdef := LieRadiusDefect.physical_defect_bound (D.μ:ℝ) hμ
    ![(D.r:ℝ),0,0] (LieSTTOutput.axis (D.model.phase t)) (value3 D.axis ![θ,0,0] t)
    (D.translation θ t).ofLp
    (LieRadiusFrame.covariantAcceleration D.model (D.translation θ)
      (D.translationVelocity θ) (D.translationAcceleration θ) t).ofLp
    ![D.model.radial t,D.model.tangent,0] θ (value D.h ![θ,0,0] t)
    (value D.radiusDeviation ![θ,0,0] t) (axis_unit _) (by simpa only [hq] using hr) hφ
    hδ hρ (by simpa only [hq] using hP) hh hH hb hs (by simpa only [hq] using he) hc (by simpa only [hq] using hR)
  rw [hq] at Hdef
  simpa only [D.physical_defect_expression hr] using Hdef

end GNC.OrbitalComparison.LieRadiusPolynomial
