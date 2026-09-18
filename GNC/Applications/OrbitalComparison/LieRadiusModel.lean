import GNC.Applications.OrbitalComparison.LieRadiusPolynomial

/-! Connect the direct certificate's executable Lie polynomial to its
inertial candidate trajectory and actual derivatives. This file adds no
assumption of group-affine inverse-square dynamics: it specifies a candidate
whose full physical defect must be bounded separately.
-/
noncomputable section
namespace GNC.OrbitalComparison.LieRadiusPolynomial
open ParameterPolynomial PointingCapPolynomial SpatialBurn VaryingRateFrame Matrix

def Input.model (D : Input) : VaryingRateBurn.Model := ⟨D.μ,D.r,D.w0,D.slope⟩
def Input.translation (D : Input) (θ : ℝ) : ℝ → E3 := vectorValue D.rho ![θ,0,0]
def Input.translationVelocity (D : Input) (θ : ℝ) : ℝ → E3 :=
  vectorValue (PointingCapPolynomial.derivative D.rho) ![θ,0,0]
def Input.translationAcceleration (D : Input) (θ : ℝ) : ℝ → E3 :=
  vectorValue (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative D.rho)) ![θ,0,0]
def Input.position (D : Input) (θ : ℝ) : ℝ → E3 :=
  LieRadiusFrame.position D.model θ (D.translation θ)
def Input.velocity (D : Input) (θ : ℝ) : ℝ → E3 :=
  LieRadiusFrame.velocity D.model θ (D.translation θ) (D.translationVelocity θ)
def Input.acceleration (D : Input) (θ : ℝ) : ℝ → E3 :=
  LieRadiusFrame.acceleration D.model θ (D.translation θ)
    (D.translationVelocity θ) (D.translationAcceleration θ)

theorem Input.translation_derivative (D : Input) (θ t : ℝ) :
    HasDerivAt (D.translation θ) (D.translationVelocity θ t) t := vector_derivative _ _ _
theorem Input.translationVelocity_derivative (D : Input) (θ t : ℝ) :
    HasDerivAt (D.translationVelocity θ) (D.translationAcceleration θ t) t := vector_derivative _ _ _
theorem Input.position_derivative (D : Input) (θ t : ℝ) :
    HasDerivAt (D.position θ) (D.velocity θ t) t :=
  LieRadiusFrame.position_derivative D.model θ (D.translation_derivative θ t)
theorem Input.velocity_derivative (D : Input) (hr : 0<(D.r:ℝ)) (θ t : ℝ) :
    HasDerivAt (D.velocity θ) (D.acceleration θ t) t :=
  LieRadiusFrame.velocity_derivative D.model hr θ
    (D.translation_derivative θ t) (D.translationVelocity_derivative θ t)

theorem Input.rate_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    value D.rate x t=D.model.rate t := by
  simp [Input.rate,VaryingRatePolynomial.time,value,termValue,monomial,
    PolynomialOrder.value,Planning.PolynomialKernel.evaluate,Input.model,VaryingRateBurn.Model.rate]
  ring

theorem Input.covariant_value (D : Input) (p : PointingCapPolynomial.Vector)
    (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (D.covariant p) x t=vectorValue (PointingCapPolynomial.derivative p) x t+
      spin (D.model.rate t) (vectorValue p x t) := by
  ext i
  fin_cases i <;> simp [vectorValue,Input.covariant,PointingCapPolynomial.derivative,
    value_add,value_subtract,value_multiply,D.rate_value,spin,pack_eq] <;> ring

theorem Input.covariant_squared_value (D : Input) (p : PointingCapPolynomial.Vector)
    (x : Fin 3 → ℝ) (t : ℝ) :
    vectorValue (D.covariant (D.covariant p)) x t=
      LieRadiusFrame.covariantAcceleration D.model (vectorValue p x)
        (vectorValue (PointingCapPolynomial.derivative p) x)
        (vectorValue (PointingCapPolynomial.derivative (PointingCapPolynomial.derivative p)) x) t := by
  have he : vectorValue (D.covariant p) x=fun s =>
      vectorValue (PointingCapPolynomial.derivative p) x s+
        spin (D.model.rate s) (vectorValue p x s) := funext (D.covariant_value p x)
  have h1 := vector_derivative (D.covariant p) x t
  have h2 := (vector_derivative (PointingCapPolynomial.derivative p) x t).add
    (spin_derivative (D.model.rate_derivative t) (vector_derivative p x t))
  change vectorValue (D.covariant p) x=
    vectorValue (PointingCapPolynomial.derivative p) x+
      (fun s => spin (D.model.rate s) (vectorValue p x s)) at he
  rw [←he] at h2
  have hd := h1.unique h2
  rw [D.covariant_value,hd,D.covariant_value]
  simp only [LieRadiusFrame.covariantAcceleration,map_add,Pi.add_apply]
  module

theorem Input.force_value (D : Input) (x : Fin 3 → ℝ) (t : ℝ) :
    LieSTTOutput.value3 D.force x t=![D.model.radial t,D.model.tangent,0] := by
  ext i
  fin_cases i <;> simp [Input.force,LieSTTOutput.value3,value_scale,
    value_subtract,value_constant,value_multiply,D.rate_value,Input.K,
    Input.model,VaryingRateBurn.Model.radial,VaryingRateBurn.Model.tangent,pow_two]

theorem Input.inverse_value (D : Input) (θ t : ℝ) :
    LieSTTOutput.value3 D.inverse ![θ,0,0] t=
      jacobianInverseQuadratic (θ • LieSTTOutput.value3 D.axis ![θ,0,0] t) ![1,0,0] := by
  have he : LieSTTOutput.value3 unitRadial ![θ,0,0] t=![1,0,0] := by
    ext i
    fin_cases i <;> simp [unitRadial,LieSTTOutput.value3,value_constant]
  ext i
  simp only [Input.inverse,LieSTTOutput.value3,value_add,value_subtract,value_scale,
    value_multiply,value_u,jacobianInverseQuadratic,Pi.add_apply,Pi.sub_apply,
    Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero]
  have hcvec := LieSTTOutput.cross_value D.axis unitRadial ![θ,0,0] t
  rw [he] at hcvec
  have hccvec := LieSTTOutput.cross_value D.axis
    (LieSTTOutput.cross D.axis unitRadial) ![θ,0,0] t
  rw [hcvec] at hccvec
  have hc := congrFun hcvec i
  have hcc := congrFun hccvec i
  simp only [LieSTTOutput.value3] at hc hcc
  rw [hc,hcc]
  simp only [map_smul,LinearMap.smul_apply,smul_smul,Pi.smul_apply,smul_eq_mul]
  have hei := congrFun he i
  simp only [LieSTTOutput.value3] at hei
  rw [hei]
  norm_num
  ring

/-- The checked residual is the covariant acceleration polynomial with the
linear inverse-radius offset and the actual polynomial-axis forcing. -/
theorem Input.residual_value (D : Input) (θ t : ℝ) :
    LieSTTOutput.value3 D.residual ![θ,0,0] t=
      (LieRadiusFrame.covariantAcceleration D.model (D.translation θ)
        (D.translationVelocity θ) (D.translationAcceleration θ) t).ofLp+
      (D.K:ℝ) • LieSTTOutput.value3 D.rho ![θ,0,0] t+
      (3*(D.K:ℝ)*value D.h ![θ,0,0] t) • LieSTTOutput.value3 D.rho ![θ,0,0] t-
      (θ • LieSTTOutput.value3 D.axis ![θ,0,0] t) ⨯₃ ![D.model.radial t,D.model.tangent,0]+
      (3*(D.K:ℝ)*(D.r:ℝ)*value D.h ![θ,0,0] t) •
        jacobianInverseQuadratic (θ • LieSTTOutput.value3 D.axis ![θ,0,0] t) ![1,0,0] := by
  have ha := congrArg WithLp.ofLp (D.covariant_squared_value D.rho ![θ,0,0] t)
  have hac : LieSTTOutput.value3 (D.covariant (D.covariant D.rho)) ![θ,0,0] t=
      (LieRadiusFrame.covariantAcceleration D.model (D.translation θ)
        (D.translationVelocity θ) (D.translationAcceleration θ) t).ofLp := by
    convert ha using 1
    ext i
    fin_cases i <;> simp [LieSTTOutput.value3,vectorValue,pack_eq]
  ext i
  have hai := congrFun hac i
  have hci := congrFun (LieSTTOutput.cross_value D.axis D.force ![θ,0,0] t) i
  rw [D.force_value] at hci
  have hwi := congrFun (D.inverse_value θ t) i
  simp only [LieSTTOutput.value3] at hai hci hwi
  simp only [LieSTTOutput.value3,Input.residual,value_subtract,value_add,value_scale,
    value_multiply,value_u,Matrix.cons_val_zero,Rat.cast_mul,Rat.cast_ofNat,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,LinearMap.smul_apply]
  rw [hai,hci,hwi]
  simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- The candidate really is the factored exponential query, evaluated at
the exact reference phase. Its polynomial axis is only a checking device. -/
theorem Input.position_factored (D : Input) (θ t : ℝ) :
    D.position θ t=D.model.reference t+turn (D.model.phase t)
      (WithLp.toLp 2 (factoredTranslation (LieSTTOutput.axis (D.model.phase t))
        (LieSTTOutput.value3 D.z ![θ,0,0] t) θ)) := by
  rw [Input.position,LieRadiusFrame.position_body]
  congr 2
  apply (WithLp.linearEquiv 2 ℝ Vec3).injective
  change Jacobian.leftAt (θ • LieSTTOutput.axis (D.model.phase t))
    (D.translation θ t).ofLp=_
  have hrho : (D.translation θ t).ofLp=θ • LieSTTOutput.value3 D.z ![θ,0,0] t := by
    have hv : (D.translation θ t).ofLp=LieSTTOutput.value3 D.rho ![θ,0,0] t := by
      ext i
      fin_cases i <;> simp [Input.translation,vectorValue,LieSTTOutput.value3,pack_eq]
    rw [hv,rho_value]
  rw [hrho,←factoredTranslation_eq _ _ (LieSTTOutput.axis_unit _)]
  rfl

/-- The stored scalar polynomial is the normalized Gram/projection radius,
not the norm of a separately expanded Cartesian polynomial witness. -/
theorem Input.radiusDeviation_value (D : Input) (θ t : ℝ) :
    value D.radiusDeviation ![θ,0,0] t=
      (LieRadiusApproximation.radiusApprox ![(D.r:ℝ),0,0]
        (LieSTTOutput.value3 D.axis ![θ,0,0] t)
        (LieSTTOutput.value3 D.z ![θ,0,0] t) θ-(D.r:ℝ)^2)/(D.r:ℝ)^2 := by
  rw [Input.radiusDeviation,value_add,value_scale,value_scale,projection_value,gram_value]
  have hp (v : Vec3) : (![(D.r:ℝ),0,0] : Vec3) ⬝ᵥ v=(D.r:ℝ)*v 0 := by
    simp [Matrix.cons_dotProduct,Matrix.vecHead]
  have hl : lengthSq (![(D.r:ℝ),0,0] : Vec3)=(D.r:ℝ)^2 := by
    change (D.r:ℝ)^2+0^2+0^2=_
    ring
  simp only [LieRadiusApproximation.radiusApprox,hl,hp,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  by_cases hr : (D.r:ℝ)=0
  · simp [hr]
  · field_simp
    ring

/-- Norm of the exact inertial candidate expressed by the scalar radius map.
The identity holds at zero pointing error as well. -/
theorem Input.position_radius (D : Input) (θ t : ℝ) :
    ‖D.position θ t‖=enorm (![(D.r:ℝ),0,0]+
      factoredTranslation (LieSTTOutput.axis (D.model.phase t))
        (LieSTTOutput.value3 D.z ![θ,0,0] t) θ) := by
  rw [D.position_factored,LieRadiusFrame.reference_body,←map_add,turn_norm]
  rw [pack_eq]
  rfl

/-- Complete normalized radius error, including the phase-axis defect and
trigonometric tails, for the candidate used by the physical ODE certificate. -/
theorem Input.radius_error_bound (D : Input) (hr : 0<(D.r:ℝ)) (θ t : ℝ)
    {δ C H : ℝ}
    (hδ : enorm (LieSTTOutput.axis (D.model.phase t)-
      LieSTTOutput.value3 D.axis ![θ,0,0] t)≤δ)
    (hC : |OcticPointing.cosineLoss θ|≤C) (hH : |θ-OcticPointing.sine θ|≤H) :
    |(‖D.position θ t‖^2/(D.r:ℝ)^2-1)-value D.radiusDeviation ![θ,0,0] t|≤
      (2/(D.r:ℝ))*LieRadiusApproximation.translationBudget |θ| δ C H*
        enorm (LieSTTOutput.value3 D.z ![θ,0,0] t)+
      (LieRadiusApproximation.gramBudget |θ| δ C/(D.r:ℝ)^2)*
        enorm (LieSTTOutput.value3 D.z ![θ,0,0] t)^2 := by
  have hq : enorm (![(D.r:ℝ),0,0] : Vec3)=(D.r:ℝ) := by
    have hn := enorm_sq (![(D.r:ℝ),0,0] : Vec3)
    change enorm (![(D.r:ℝ),0,0] : Vec3)^2=(D.r:ℝ)^2+0^2+0^2 at hn
    norm_num only [zero_pow,add_zero] at hn
    nlinarith [enorm_nonneg (![(D.r:ℝ),0,0] : Vec3)]
  have hs := LieRadiusApproximation.radius_error ![(D.r:ℝ),0,0]
    (LieSTTOutput.axis (D.model.phase t)) (LieSTTOutput.value3 D.axis ![θ,0,0] t)
    (LieSTTOutput.value3 D.z ![θ,0,0] t) (LieSTTOutput.axis_unit _) θ hδ hC hH
  rw [hq] at hs
  rw [D.radiusDeviation_value,D.position_radius]
  have hnorm (X Y : ℝ) : X/(D.r:ℝ)^2-1-(Y-(D.r:ℝ)^2)/(D.r:ℝ)^2=
      (X-Y)/(D.r:ℝ)^2 := by field_simp; ring
  rw [hnorm,abs_div,abs_of_nonneg (sq_nonneg (D.r:ℝ))]
  apply (div_le_div_of_nonneg_right hs (sq_nonneg (D.r:ℝ))).trans_eq
  field_simp

end GNC.OrbitalComparison.LieRadiusPolynomial
