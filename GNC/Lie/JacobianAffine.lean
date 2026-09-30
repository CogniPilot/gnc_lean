import GNC.Dynamics.LieRadiusQuadratic

/-! A finite, division-free first-degree Jacobian reconstruction, with its
operator error charged explicitly. This is an approximation of the final
geometric map, not a change to the retained error dynamics. -/
noncomputable section
namespace GNC.JacobianAffine
open Matrix

def apply (φ v : Vec3) : Vec3 := v+(1/2:ℝ) • (φ ⨯₃ v)
def tail (s : ℝ) : ℝ := s^2/6+LieRadiusQuadratic.tail s

theorem tail_nonneg {s : ℝ} (hs : 0≤s) : 0≤tail s := by
  unfold tail LieRadiusQuadratic.tail
  positivity

theorem tail_mono {s t : ℝ} (hs : 0≤s) (hst : s≤t) : tail s≤tail t := by
  unfold tail LieRadiusQuadratic.tail
  gcongr

theorem error_bound (φ v : Vec3) :
    enorm (Jacobian.leftAt φ v-apply φ v)≤tail (enorm φ)*enorm v := by
  have hc := (cross_enorm_le φ (φ ⨯₃ v)).trans
    (mul_le_mul_of_nonneg_left (cross_enorm_le φ v) (enorm_nonneg φ))
  have he : Jacobian.leftAt φ v-apply φ v =
      (Jacobian.leftAt φ v-LieRadiusQuadratic.apply φ v)+
      (1/6:ℝ) • (φ ⨯₃ (φ ⨯₃ v)) := by
    dsimp [apply, LieRadiusQuadratic.apply]
    module
  rw [he]
  apply (enorm_add_le _ _).trans
  have hh := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤1/6 by norm_num)
  rw [enorm_smul]
  rw [abs_of_pos (by norm_num : (0:ℝ)<1/6)]
  convert add_le_add (LieRadiusQuadratic.error_bound φ v) hh using 1 <;>
    dsimp [tail] <;> ring

/-- Matched Cartesian quadratic-angle forcing bound, including zero angle. -/
theorem rotation_quadratic_bound (φ u : Vec3) :
    enorm (rotate (rotationExp φ) u-u-
      (φ ⨯₃ u+(1/2:ℝ) • (φ ⨯₃ (φ ⨯₃ u))))≤
      tail (enorm φ)*enorm φ*enorm u := by
  have h := error_bound φ (φ ⨯₃ u)
  rw [leftAt_cross_rotation] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (cross_enorm_le φ u)
    (tail_nonneg (enorm_nonneg φ))).trans_eq (by ring))

/-- Transfer any exact-geometric position certificate to the inexpensive
finite reconstruction. Its truncation is an explicit additional term. -/
theorem prediction_bound (φ x q y : Vec3) {θ L B : ℝ}
    (hφ : enorm φ≤θ) (hy : enorm y≤L)
    (h : enorm (x-(q+Jacobian.leftAt φ y))≤B) :
    enorm (x-(q+apply φ y))≤B+tail θ*L := by
  have ht := tail_mono (enorm_nonneg φ) hφ
  have hn := tail_nonneg ((enorm_nonneg φ).trans hφ)
  have hb := (error_bound φ y).trans (mul_le_mul ht hy (enorm_nonneg y) hn)
  have he : x-(q+apply φ y)=(x-(q+Jacobian.leftAt φ y))+
      (Jacobian.leftAt φ y-apply φ y) := by abel
  rw [he]
  exact (enorm_add_le _ _).trans (add_le_add h hb)

end GNC.JacobianAffine
