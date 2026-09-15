import GNC.Lie.AxisRotation

/-! Full three-dimensional pointing, including an out-of-plane tilt.
The two angles parameterize a thrust direction, not a restriction of the
attitude state to SO(2). The rotations themselves are elements of SO(3).
-/
noncomputable section
namespace GNC.SpatialPointing
open Matrix Real
open scoped Matrix

def yMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos a,0,sin a; 0,1,0; -sin a,0,cos a]

theorem y_orthogonal (a : ℝ) : (yMatrix a).transpose*yMatrix a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yMatrix,mul_apply,Fin.sum_univ_succ] <;> nlinarith [sin_sq_add_cos_sq a]

theorem y_det (a : ℝ) : (yMatrix a).det = 1 := by
  simp [yMatrix,det_fin_three,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  nlinarith [sin_sq_add_cos_sq a]

def yRotation (a : ℝ) : SO3 :=
  ⟨yMatrix a,(mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (y_orthogonal a),y_det a⟩

/-- Positive elevation tilts the reference radial thrust toward +z. -/
def attitude (azimuth elevation : ℝ) : SO3 :=
  AxisRotation.zRotation azimuth*yRotation (-elevation)

def direction (azimuth elevation : ℝ) : Vec3 :=
  rotate (attitude azimuth elevation) ![1,0,0]

theorem direction_components (a b : ℝ) :
    direction a b = ![cos a*cos b,sin a*cos b,sin b] := by
  ext i
  fin_cases i <;>
    simp [direction,attitude,rotate,AxisRotation.zRotation,AxisRotation.zMatrix,
      yRotation,yMatrix,mul_apply,mulVec, dotProduct,Fin.sum_univ_succ]

/-- The exact three-dimensional replacement for the planar circle identity. -/
theorem direction_unit (a b : ℝ) :
    (direction a b) ⬝ᵥ (direction a b) = 1 := by
  rw [dot_self_lengthSq]
  change lengthSq (rotate (attitude a b) ![1,0,0]) = 1
  rw [rotate_lengthSq]
  change (1:ℝ)^2+0^2+0^2 = 1
  norm_num

theorem sphere_relation (a b : ℝ) :
    (sin a*cos b)^2+(sin b)^2 =
      2*(1-cos a*cos b)-(1-cos a*cos b)^2 := by
  have h := direction_unit a b
  rw [direction_components] at h
  simp [dotProduct,Fin.sum_univ_succ] at h
  nlinarith

theorem force_error_sq (a b : ℝ) :
    enorm (direction a b-![1,0,0])^2 = 2*(1-cos a*cos b) := by
  rw [enorm_sq,direction_components]
  change (cos a*cos b-1)^2+(sin a*cos b-0)^2+(sin b-0)^2 = _
  simp only [sub_zero]
  nlinarith [sphere_relation a b]

/-- Changing rotation order changes the thrust's normal component. -/
theorem order_changes_normal (a b : ℝ) :
    (direction a b) 2-
      (rotate (yRotation (-b)*AxisRotation.zRotation a) ![1,0,0]) 2 =
      (1-cos a)*sin b := by
  rw [direction_components]
  simp [rotate,yRotation,yMatrix,AxisRotation.zRotation,AxisRotation.zMatrix,
    mul_apply,mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem planar_restriction (a : ℝ) : direction a 0 = ![cos a,sin a,0] := by
  simp [direction_components]

theorem tilted_thrust_not_planar {a b : ℝ} (hb : sin b ≠ 0) :
    (direction a b) 2 ≠ 0 := by simpa [direction_components] using hb

theorem force_error_angle_bound (a b : ℝ) :
    enorm (direction a b-![1,0,0])^2 ≤ a^2+b^2 := by
  rw [force_error_sq]
  have h := mul_nonneg (sub_nonneg.mpr (cos_le_one a)) (sub_nonneg.mpr (cos_le_one b))
  nlinarith [one_sub_sq_div_two_le_cos (x := a),one_sub_sq_div_two_le_cos (x := b)]

end GNC.SpatialPointing
