import GNC.Dynamics.LieRadiusCertificate
import GNC.Applications.OrbitalComparison.LieSTTOutput

/-! Exact physical reconstruction for the direct Lie-coordinate certificate.
The inertial pointing axis is fixed while its reference-frame coordinates
vary. Differentiating in the inertial frame avoids differentiating an
approximate exponential map; the rotating-frame acceleration retains both
Coriolis terms, the Euler term, and the centripetal term.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.OrbitalComparison.LieRadiusFrame
open SpatialBurn VaryingRateBurn VaryingRateFrame Matrix Real

def left (φ : Vec3) : E3 →ₗ[ℝ] E3 where
  toFun x := WithLp.toLp 2 (Jacobian.leftAt φ x.ofLp)
  map_add' x y := by
    apply (WithLp.linearEquiv 2 ℝ Vec3).injective
    exact Jacobian.leftAt_add φ x.ofLp y.ofLp
  map_smul' a x := by
    apply (WithLp.linearEquiv 2 ℝ Vec3).injective
    exact Jacobian.leftAt_smul φ x.ofLp a

theorem left_derivative (φ : Vec3) {f : ℝ → E3} {v : E3} {t : ℝ}
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => left φ (f s)) (left φ v) t :=
  (left φ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

theorem left_norm (φ : Vec3) (hφ : enorm φ<2*π) (x : E3) :
    ‖left φ x‖≤‖x‖ := leftAt_nonexpansive φ x.ofLp hφ

def inertialAxis : Vec3 := ![0,-3/5,4/5]

theorem axis_rotated (ψ : ℝ) :
    rotate (AxisRotation.zRotation ψ) (LieSTTOutput.axis ψ)=inertialAxis := by
  ext i
  fin_cases i <;> simp [rotate,AxisRotation.zRotation,AxisRotation.zMatrix,
    LieSTTOutput.axis,inertialAxis,mulVec,dotProduct,Fin.sum_univ_succ] <;>
    nlinarith [sin_sq_add_cos_sq ψ]

theorem turn_left (ψ θ : ℝ) (x : E3) :
    turn ψ (left (θ • LieSTTOutput.axis ψ) x)=
      left (θ • inertialAxis) (turn ψ x) := by
  apply (WithLp.linearEquiv 2 ℝ Vec3).injective
  change (turn ψ (WithLp.toLp 2 (Jacobian.leftAt (θ • LieSTTOutput.axis ψ) x.ofLp))).ofLp=_
  rw [turn_matrix]
  change rotate (AxisRotation.zRotation ψ) (Jacobian.leftAt (θ • LieSTTOutput.axis ψ) x.ofLp)=_
  rw [←leftAt_rotation_equivariant,rotate_smul,axis_rotated]
  congr 1
  exact (turn_matrix ψ x.ofLp).symm

def position (m : Model) (θ : ℝ) (ρ : ℝ → E3) (t : ℝ) : E3 :=
  m.reference t+left (θ • inertialAxis) (turn (m.phase t) (ρ t))

def velocity (m : Model) (θ : ℝ) (ρ ρv : ℝ → E3) (t : ℝ) : E3 :=
  m.referenceVelocity t+
    left (θ • inertialAxis) (turn (m.phase t) (ρv t+spin (m.rate t) (ρ t)))

def covariantAcceleration (m : Model) (ρ ρv ρa : ℝ → E3) (t : ℝ) : E3 :=
  ρa t+(2:ℝ) • spin (m.rate t) (ρv t)+spin m.slope (ρ t)+
    spin (m.rate t) (spin (m.rate t) (ρ t))

def acceleration (m : Model) (θ : ℝ) (ρ ρv ρa : ℝ → E3) (t : ℝ) : E3 :=
  Gravity.field m.μ (m.reference t)+m.nominalThrust t+
    left (θ • inertialAxis) (turn (m.phase t) (covariantAcceleration m ρ ρv ρa t))

theorem position_body (m : Model) (θ : ℝ) (ρ : ℝ → E3) (t : ℝ) :
    position m θ ρ t=m.reference t+
      turn (m.phase t) (left (θ • LieSTTOutput.axis (m.phase t)) (ρ t)) := by
  rw [position,turn_left]

theorem position_derivative (m : Model) (θ : ℝ) {ρ ρv : ℝ → E3} {t : ℝ}
    (hρ : HasDerivAt ρ (ρv t) t) :
    HasDerivAt (position m θ ρ) (velocity m θ ρ ρv t) t :=
  (m.reference_derivative t).add
    (left_derivative (θ • inertialAxis) (turn_derivative (m.phase_derivative t) hρ))

theorem velocity_derivative (m : Model) (hr : 0<m.r) (θ : ℝ)
    {ρ ρv ρa : ℝ → E3} {t : ℝ}
    (hρ : HasDerivAt ρ (ρv t) t) (hv : HasDerivAt ρv (ρa t) t) :
    HasDerivAt (velocity m θ ρ ρv) (acceleration m θ ρ ρv ρa t) t := by
  have h := (m.referenceVelocity_derivative hr t).add
    (left_derivative (θ • inertialAxis) (turn_derivative (m.phase_derivative t)
      (hv.add (spin_derivative (m.rate_derivative t) hρ))))
  convert h using 1
  simp only [acceleration,covariantAcceleration,Pi.add_apply,map_add,map_smul]
  module

theorem reference_body (m : Model) (t : ℝ) :
    m.reference t=turn (m.phase t) (pack m.r 0 0) := by
  ext i
  fin_cases i <;> simp [Model.reference,VaryingRateReference.position,
    turn,SpatialRotatingFrame.mix,pack_eq]

theorem turn_gravity (μ ψ : ℝ) (x : E3) :
    Gravity.field μ (turn ψ x)=turn ψ (Gravity.field μ x) := by
  simp [Gravity.field,map_smul,turn_norm]

theorem first_cross (ψ x y : ℝ) :
    (VaryingRateForcing.first (RotationPhaseCertificate.phase ψ) x y).ofLp=
      LieSTTOutput.axis ψ ⨯₃ ![x,y,0] := by
  rw [VaryingRateForcing.first_physical]
  ext i
  fin_cases i <;>
    simp [VaryingRateReference.firstForce,LieSTTOutput.axis,cross_apply] <;> ring

theorem second_cross (ψ x y : ℝ) :
    (VaryingRateForcing.second (RotationPhaseCertificate.phase ψ)
      (RotationPhaseCertificate.phase (2*ψ)) x y).ofLp=
      LieSTTOutput.axis ψ ⨯₃ (LieSTTOutput.axis ψ ⨯₃ ![x,y,0]) := by
  rw [VaryingRateForcing.second_physical]
  ext i
  fin_cases i <;>
    simp [VaryingRateReference.secondForce,LieSTTOutput.axis,cross_apply,
      sin_two_mul,cos_two_mul]
  · ring
  · linear_combination (9/25)*y*(sin_sq_add_cos_sq ψ)
  · ring

theorem source_left (θ ψ x y : ℝ) :
    VaryingRateForcing.source θ ψ x y=
      left (θ • LieSTTOutput.axis ψ)
        (WithLp.toLp 2 ((θ • LieSTTOutput.axis ψ) ⨯₃ ![x,y,0])) := by
  apply (WithLp.linearEquiv 2 ℝ Vec3).injective
  change (VaryingRateForcing.source θ ψ x y).ofLp=
    Jacobian.leftAt (θ • LieSTTOutput.axis ψ) ((θ • LieSTTOutput.axis ψ) ⨯₃ ![x,y,0])
  have h3 : LieSTTOutput.axis ψ ⨯₃ (LieSTTOutput.axis ψ ⨯₃
      (LieSTTOutput.axis ψ ⨯₃ ![x,y,0]))= -(LieSTTOutput.axis ψ ⨯₃ ![x,y,0]) := by
    have h := Axis.cross_sq (LieSTTOutput.axis ψ) ![x,y,0] (LieSTTOutput.axis_unit ψ)
    rw [h]
    simp only [map_sub,Axis.cross_axial,zero_sub]
  simp only [map_smul,LinearMap.smul_apply]
  rw [←factoredTranslation_eq _ _ (LieSTTOutput.axis_unit ψ)]
  change sin θ • (VaryingRateForcing.first (RotationPhaseCertificate.phase ψ) x y).ofLp+
    (1-cos θ) • (VaryingRateForcing.second (RotationPhaseCertificate.phase ψ)
      (RotationPhaseCertificate.phase (2*ψ)) x y).ofLp=_
  rw [first_cross,second_cross]
  simp only [factoredTranslation,h3]
  module

/-- Exact equality of inertial and reference-frame physical defects. -/
theorem physical_defect_norm (m : Model) (hr : 0<m.r) (θ : ℝ)
    (ρ ρv ρa : ℝ → E3) (t : ℝ) :
    ‖acceleration m θ ρ ρv ρa t-m.acceleration θ t (position m θ ρ t)‖=
    ‖Gravity.field m.μ (pack m.r 0 0)+pack (m.radial t) m.tangent 0+
      left (θ • LieSTTOutput.axis (m.phase t)) (covariantAcceleration m ρ ρv ρa t)-
      (Gravity.field m.μ (pack m.r 0 0+
        left (θ • LieSTTOutput.axis (m.phase t)) (ρ t))+
        (pack (m.radial t) m.tangent 0+m.source θ t))‖ := by
  have hp : position m θ ρ t=turn (m.phase t)
      (pack m.r 0 0+left (θ • LieSTTOutput.axis (m.phase t)) (ρ t)) := by
    rw [position_body,reference_body,map_add]
  rw [acceleration,Model.acceleration,hp,turn_gravity,reference_body,turn_gravity,
    nominalThrust_components m hr,←turn_left,Model.thrust,Model.relativeThrust,
    nominalThrust_components m hr]
  simp only [←map_add,←map_sub,turn_norm]

/-- The direct Lie residual bounds the actual nonlinear acceleration defect.
The nonnegative inverse-radius branch and candidate radius floor are explicit.
No Cartesian expansion of the candidate is required. -/
theorem physical_defect_bound (m : Model) (hμ : 0≤m.μ) (hr : 0<m.r) (θ : ℝ)
    (ρ ρv ρa : ℝ → E3) (t u : ℝ) (w : Vec3)
    (hφ : enorm (θ • LieSTTOutput.axis (m.phase t))<2*π) {floor A : ℝ}
    (hf : 0<floor)
    (hfloor : floor≤enorm (![m.r,0,0]+
      Jacobian.leftAt (θ • LieSTTOutput.axis (m.phase t)) (ρ t).ofLp))
    (hu : 0≤u)
    (hA : enorm (![m.r,0,0]+
      Jacobian.leftAt (θ • LieSTTOutput.axis (m.phase t)) (ρ t).ofLp)*u≤A) :
    ‖acceleration m θ ρ ρv ρa t-m.acceleration θ t (position m θ ρ t)‖≤
      enorm ((covariantAcceleration m ρ ρv ρa t).ofLp+(m.μ*u^3) • (ρ t).ofLp-
        (θ • LieSTTOutput.axis (m.phase t)) ⨯₃ ![m.radial t,m.tangent,0]+
        (m.μ*u^3-Gravity.radialGain m.μ ![m.r,0,0]) • w)+
      |m.μ*u^3-Gravity.radialGain m.μ ![m.r,0,0]| *
        enorm (![m.r,0,0]-Jacobian.leftAt (θ • LieSTTOutput.axis (m.phase t)) w)+
      m.μ*Gravity.inverseRadiusFactor A/floor^2*
        |enorm (![m.r,0,0]+Jacobian.leftAt (θ • LieSTTOutput.axis (m.phase t)) (ρ t).ofLp)^2*u^2-1| := by
  have hs : ![m.radial t,m.tangent,0]+(m.source θ t).ofLp=
      rotate (rotationExp (θ • LieSTTOutput.axis (m.phase t))) ![m.radial t,m.tangent,0] := by
    change ![m.radial t,m.tangent,0]+(VaryingRateForcing.source θ (m.phase t)
      (m.radial t) m.tangent).ofLp=_
    rw [source_left]
    change ![m.radial t,m.tangent,0]+
      Jacobian.leftAt (θ • LieSTTOutput.axis (m.phase t))
        ((θ • LieSTTOutput.axis (m.phase t)) ⨯₃ ![m.radial t,m.tangent,0])=_
    rw [leftAt_cross_rotation]
    module
  rw [physical_defect_norm m hr]
  simp only [pack_eq]
  change enorm (Gravity.field3 m.μ ![m.r,0,0]+![m.radial t,m.tangent,0]+
    Jacobian.leftAt (θ • LieSTTOutput.axis (m.phase t))
      (covariantAcceleration m ρ ρv ρa t).ofLp-
    (Gravity.field3 m.μ (![m.r,0,0]+Jacobian.leftAt (θ • LieSTTOutput.axis (m.phase t)) (ρ t).ofLp)+
      (![m.radial t,m.tangent,0]+(m.source θ t).ofLp)))≤_
  rw [hs]
  exact Gravity.lie_acceleration_defect_bound m.μ u hμ _ _ _ _ _ w hφ hf hfloor hu hA

end GNC.OrbitalComparison.LieRadiusFrame
