import GNC.Applications.OrbitalComparison.CenteredResponseBounds
import GNC.Lie.RotationIsometry

/-! Exact half-rotation reconstruction of the computed Cartesian candidate,
its derivatives, its physical midpoint initial data and full-gravity defect.
The physical thrust is rotated by the full attitude offset. -/
noncomputable section
set_option maxHeartbeats 0
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set

def centeredPosition (φ : Vec3) (t : ℝ) : E3 :=
  nominal t+(firstResponse (rotationWeights φ) t+secondResponse (rotationWeights φ) t)
def centeredVelocity (φ : Vec3) (t : ℝ) : E3 :=
  JointErrorData.referenceVelocity t+(firstVelocity (rotationWeights φ) t+secondVelocity (rotationWeights φ) t)
def centeredAcceleration (φ : Vec3) (t : ℝ) : E3 :=
  Gravity.field (K:ℝ) (nominal t)+WithLp.toLp 2 (JointErrorData.exactForce t)+
    (firstAcceleration (rotationWeights φ) t+secondAcceleration (rotationWeights φ) t)
def centeredThrust (φ : Vec3) (t : ℝ) : E3 :=
  WithLp.toLp 2 (rotate (halfRotation φ) (JointErrorData.exactForce t))

def position (φ : Vec3) (t : ℝ) : E3 := rotationIsometry (halfRotation φ) (centeredPosition φ t)
def velocity (φ : Vec3) (t : ℝ) : E3 := rotationIsometry (halfRotation φ) (centeredVelocity φ t)
def acceleration (φ : Vec3) (t : ℝ) : E3 := rotationIsometry (halfRotation φ) (centeredAcceleration φ t)
def thrust (φ : Vec3) (t : ℝ) : E3 := WithLp.toLp 2 (rotate (rotationExp φ) (JointErrorData.exactForce t))

theorem centered_thrust_split (φ : Vec3) (t : ℝ) :
    centeredThrust φ t=WithLp.toLp 2 (JointErrorData.exactForce t)+forceDifference φ t := by
  simp only [centeredThrust,forceDifference,WithLp.toLp_sub]
  module

theorem centered_position_derivative (φ : Vec3) (t : ℝ) :
    HasDerivAt (centeredPosition φ) (centeredVelocity φ t) t :=
  (JointErrorData.reference_position_derivative t).add
    ((first_response_derivative _ t).add (second_response_derivative _ t))

theorem centered_velocity_derivative (φ : Vec3) (t : ℝ) :
    HasDerivAt (centeredVelocity φ) (centeredAcceleration φ t) t :=
  (JointErrorData.reference_velocity_derivative t).add
    ((first_velocity_derivative _ t).add (second_velocity_derivative _ t))

theorem position_derivative (φ : Vec3) (t : ℝ) :
    HasDerivAt (position φ) (velocity φ t) t :=
  rotation_isometry_derivative _ (centered_position_derivative φ t)

theorem velocity_derivative (φ : Vec3) (t : ℝ) :
    HasDerivAt (velocity φ) (acceleration φ t) t :=
  rotation_isometry_derivative _ (centered_velocity_derivative φ t)

theorem thrust_rotation (φ : Vec3) (t : ℝ) :
    thrust φ t=rotationIsometry (halfRotation φ) (centeredThrust φ t) := by
  change WithLp.toLp 2 (rotate (rotationExp φ) (JointErrorData.exactForce t))=
    WithLp.toLp 2 (rotate (halfRotation φ) (rotate (halfRotation φ) (JointErrorData.exactForce t)))
  rw [←rotate_mul]
  change _=WithLp.toLp 2 (rotate
    (rotationExp ((1/2:ℝ) • φ)*rotationExp ((1/2:ℝ) • φ)) (JointErrorData.exactForce t))
  rw [RotationCenteredError.half_square]

theorem position_initial (φ : Vec3) :
    position φ 0=WithLp.toLp 2 (RotationCenteredError.midpoint
      (rotationExp φ) JointErrorData.initialReferencePosition) := by
  rw [position,centeredPosition,second_initial_value,add_zero,first_initial_centered]
  change WithLp.toLp 2 (rotate (halfRotation φ)
    (JointErrorData.exactReference 0+
      RotationCenteredError.centered φ JointErrorData.initialReferencePosition))=_
  rw [JointErrorData.reference_initial_position,RotationCenteredError.centered]
  simp only [halfRotation,add_sub_cancel,←rotate_mul,mul_inv_cancel,rotate_one]

theorem velocity_initial (φ : Vec3) :
    velocity φ 0=WithLp.toLp 2 (RotationCenteredError.midpoint
      (rotationExp φ) JointErrorData.initialReferenceVelocity) := by
  rw [velocity,centeredVelocity,second_initial_velocity_value,add_zero,first_velocity_initial_centered]
  change WithLp.toLp 2 (rotate (halfRotation φ)
    ((JointErrorData.referenceVelocity 0).ofLp+
      RotationCenteredError.centered φ JointErrorData.initialReferenceVelocity))=_
  rw [JointErrorData.reference_initial_velocity,RotationCenteredError.centered]
  simp only [halfRotation,add_sub_cancel,←rotate_mul,mul_inv_cancel,rotate_one]

theorem centered_position_radius (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    1-(displacementRange:ℝ)≤‖centeredPosition φ t‖ := by
  have hb := (norm_add_le (firstResponse (rotationWeights φ) t)
    (secondResponse (rotationWeights φ) t)).trans
    (add_le_add (first_response_bound φ hφ ht) (second_response_bound φ hφ ht))
  have h := norm_sub_le (centeredPosition φ t)
    (firstResponse (rotationWeights φ) t+secondResponse (rotationWeights φ) t)
  rw [centeredPosition,add_sub_cancel_right,nominal_norm] at h
  change 1≤‖centeredPosition φ t‖+
    ‖firstResponse (rotationWeights φ) t+secondResponse (rotationWeights φ) t‖ at h
  simp only [displacementRange,Rat.cast_add]
  linarith

theorem position_radius (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 1-(displacementRange:ℝ)≤‖position φ t‖ := by
  rw [position,(rotationIsometry _).norm_map]
  exact centered_position_radius φ hφ ht

theorem centered_physical_defect (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖centeredAcceleration φ t-(Gravity.field (K:ℝ) (centeredPosition φ t)+centeredThrust φ t)‖≤
      (defectMagnitude:ℝ) := by
  have hk : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have hregion : (firstRange:ℝ)+(secondRange:ℝ)<1 := by
    have h : 0<(displacementRange:ℝ) ∧ 2*(displacementRange:ℝ)<1 := by
      exact_mod_cast region_checked.2.2
    simp only [displacementRange,Rat.cast_add] at h
    linarith
  have h₁ := first_rotation_defect φ hφ ht
  have h₂ := second_rotation_defect φ hφ ht
  rw [norm_sub_rev] at h₁ h₂
  have h := Gravity.quadratic_response_defect_bound (K:ℝ) 1 hk (by norm_num)
    (nominal t) (firstResponse (rotationWeights φ) t) (secondResponse (rotationWeights φ) t)
    (Gravity.field (K:ℝ) (nominal t)+WithLp.toLp 2 (JointErrorData.exactForce t))
    (firstAcceleration (rotationWeights φ) t) (secondAcceleration (rotationWeights φ) t)
    (WithLp.toLp 2 (JointErrorData.exactForce t)) (forceDifference φ t)
    (r := 1) (ε₀ := 0) (by rw [nominal_norm]) hregion
    (first_response_bound φ hφ ht) (second_response_bound φ hφ ht)
    (by simp only [one_smul,sub_self,norm_zero,le_refl])
    (by simpa only [one_smul] using h₁) (by simpa only [one_smul] using h₂)
  simp only [one_smul] at h
  have hb := (Rat.cast_le (K := ℝ)).mpr physical_budget_checked
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat,
    Rat.cast_one] at hb
  rw [centered_thrust_split,centeredAcceleration,centeredPosition,norm_sub_rev]
  apply h.trans
  simpa only [one_mul,one_pow,div_one,zero_add,displacementRange,Rat.cast_add,
    div_mul_eq_mul_div,add_assoc] using hb

theorem physical_defect (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖acceleration φ t-(Gravity.field (K:ℝ) (position φ t)+thrust φ t)‖≤(defectMagnitude:ℝ) := by
  rw [position,acceleration,thrust_rotation,OrbitalSymmetry.gravity_equivariant,
    ←map_add,←map_sub,(rotationIsometry _).norm_map]
  exact centered_physical_defect φ hφ ht

end GNC.OrbitalComparison.CenteredResponseData
