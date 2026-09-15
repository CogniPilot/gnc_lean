import GNC.Lie.SpatialPointing
import GNC.Dynamics.GravityLinearization

/-!
Out-of-plane thrust for the same-body-input convention of the orbital paper.
A constant inertial attitude offset left-multiplies the reference attitude.
It is generally time varying in the reference's rotating orbital frame.
The cross-track equation below retains the complete inverse-square field.
-/
noncomputable section
namespace GNC.OrbitalComparison.SpatialPointing
open Matrix Real
open scoped Matrix Matrix.Norms.Operator

def referenceDirection (phase : ℝ) : Vec3 := ![cos phase,sin phase,0]

def burnDirection (a b phase : ℝ) : Vec3 :=
  rotate (GNC.SpatialPointing.attitude a b) (referenceDirection phase)

def forceError (a b acceleration phase : ℝ) : Vec3 :=
  acceleration • (burnDirection a b phase-referenceDirection phase)

theorem burn_components (a b phase : ℝ) :
    burnDirection a b phase =
      ![cos a*cos b*cos phase-sin a*sin phase,
        sin a*cos b*cos phase+cos a*sin phase,sin b*cos phase] := by
  ext i
  fin_cases i <;>
    simp [burnDirection,referenceDirection,GNC.SpatialPointing.attitude,rotate,
      AxisRotation.zRotation,AxisRotation.zMatrix,GNC.SpatialPointing.yRotation,
      GNC.SpatialPointing.yMatrix,mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

/-- This family has the reference's body angular velocity, including when
the inertial attitude offset tilts thrust out of the orbital plane. -/
theorem matched_body_rate (a b : ℝ) {phase : ℝ → ℝ} {ω t : ℝ}
    (hphase : HasDerivAt phase ω t) :
    HasDerivAt (fun s => (GNC.SpatialPointing.attitude a b*
      AxisRotation.zRotation (phase s)).val)
      ((GNC.SpatialPointing.attitude a b*AxisRotation.zRotation (phase t)).val*
        skew ![0,0,ω]) t := by
  have h := (hasDerivAt_const t (GNC.SpatialPointing.attitude a b).val).mul
    (AxisRotation.z_derivative hphase)
  convert h using 1
  simp [Matrix.mul_assoc]

theorem normal_force (a b acceleration phase : ℝ) :
    (forceError a b acceleration phase) 2 = acceleration*sin b*cos phase := by
  rw [forceError,burn_components]
  change acceleration*(sin b*cos phase-0) = _
  ring

/-- Unlike a fixed orbital-frame tilt, a fixed inertial tilt has a normal
forcing proportional to cos(phase). It is not a constant normal input. -/
theorem normal_force_derivative (a b acceleration : ℝ)
    {phase : ℝ → ℝ} {ω t : ℝ} (hphase : HasDerivAt phase ω t) :
    HasDerivAt (fun s => (forceError a b acceleration (phase s)) 2)
      (-acceleration*sin b*sin (phase t)*ω) t := by
  simp_rw [normal_force]
  convert hphase.cos.const_mul (acceleration*sin b) using 1 <;> ring

def physicalAcceleration (μ radius a b acceleration phase : ℝ) (d : Vec3) : Vec3 :=
  Gravity.field3 μ (radius • referenceDirection phase+d)-
    Gravity.field3 μ (radius • referenceDirection phase)+forceError a b acceleration phase

/-- No planar gravity approximation: the denominator includes the normal
displacement through the norm of the complete position vector. -/
theorem cross_track_acceleration (μ radius a b acceleration phase : ℝ) (d : Vec3) :
    (physicalAcceleration μ radius a b acceleration phase d) 2 =
      -μ/(enorm (radius • referenceDirection phase+d))^3*d 2+
        acceleration*sin b*cos phase := by
  change (-μ/(enorm (radius • referenceDirection phase+d))^3)*
      (radius*(referenceDirection phase) 2+d 2)-
      (-μ/(enorm (radius • referenceDirection phase))^3)*
      (radius*(referenceDirection phase) 2)+(forceError a b acceleration phase) 2 = _
  rw [normal_force]
  change _*(radius*0+d 2)-_*(radius*0)+_ = _
  ring

theorem full_position_norm_sq (radius phase : ℝ) (d : Vec3) :
    enorm (radius • referenceDirection phase+d)^2 =
      (radius*cos phase+d 0)^2+(radius*sin phase+d 1)^2+(d 2)^2 := by
  rw [enorm_sq]
  change (radius*cos phase+d 0)^2+(radius*sin phase+d 1)^2+(radius*0+d 2)^2 = _
  ring

/-- Starting in the orbital plane does not justify discarding normal
acceleration when thrust is tilted out of it. -/
theorem initially_nonplanar (μ radius a b acceleration : ℝ)
    (ha : acceleration ≠ 0) (hb : sin b ≠ 0) :
    (physicalAcceleration μ radius a b acceleration 0 0) 2 ≠ 0 := by
  rw [cross_track_acceleration]
  simpa using mul_ne_zero ha hb

/-- A direction fixed in the reference RTN frame, including its pointing
offset. This is a different uncertainty convention from `burnDirection`. -/
def rtnFixedDirection (a b phase : ℝ) : Vec3 :=
  rotate (AxisRotation.zRotation phase) (GNC.SpatialPointing.direction a b)

theorem rtn_fixed_normal (a b phase : ℝ) :
    (rtnFixedDirection a b phase) 2 = sin b := by
  rw [rtnFixedDirection,GNC.SpatialPointing.direction_components]
  simp [rotate,AxisRotation.zRotation,AxisRotation.zMatrix,mulVec,dotProduct,
    Fin.sum_univ_succ]

theorem offset_convention_difference (a b phase : ℝ) :
    (rtnFixedDirection a b phase) 2-(burnDirection a b phase) 2 =
      sin b*(1-cos phase) := by
  rw [rtn_fixed_normal,burn_components]
  change sin b-sin b*cos phase = _
  ring

/-- Holding the offset fixed in the RTN frame conjugates the commanded
body rate; it must not silently inherit the matched-rate assumption. -/
theorem rtn_fixed_body_rate (a b : ℝ) {phase : ℝ → ℝ} {ω t : ℝ}
    (hphase : HasDerivAt phase ω t) :
    HasDerivAt (fun s => (AxisRotation.zRotation (phase s)*
      GNC.SpatialPointing.attitude a b).val)
      ((AxisRotation.zRotation (phase t)*GNC.SpatialPointing.attitude a b).val*
        skew (rotate (GNC.SpatialPointing.attitude a b)⁻¹ ![0,0,ω])) t := by
  have hc : HasDerivAt (fun _ : ℝ => (GNC.SpatialPointing.attitude a b).val)
      ((GNC.SpatialPointing.attitude a b).val*skew (0:Vec3)) t := by
    simpa [skew_zero] using hasDerivAt_const t (GNC.SpatialPointing.attitude a b).val
  simpa using AxisRotation.product_derivative (AxisRotation.z_derivative hphase) hc

/-- With an inertially fixed nominal attitude, both constant-offset
conventions give the same constant direction. The reference orbit must
still solve its own inverse-square-plus-constant-thrust equation. -/
theorem inertially_fixed_direction (a b : ℝ) :
    burnDirection a b 0 = GNC.SpatialPointing.direction a b ∧
      rtnFixedDirection a b 0 = GNC.SpatialPointing.direction a b := by
  constructor
  · simp [burnDirection,referenceDirection,GNC.SpatialPointing.direction]
  · simp [rtnFixedDirection,rotate_one]

end GNC.OrbitalComparison.SpatialPointing
