import GNC.Lie.ExponentialCoordinates

/-! Theorem 1's gravity decomposition for the actual inverse-square field,
including the rotation into the reference body frame. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC

theorem rotate_smul (R : SO3) (a : ℝ) (v : Vec3) : rotate R (a • v) = a • rotate R v := by
  simp [rotate, Matrix.mulVec_smul]

theorem rotate_dot (R : SO3) (u v : Vec3) : rotate R u ⬝ᵥ rotate R v = u ⬝ᵥ v := by
  change (R.val *ᵥ u) ⬝ᵥ (R.val *ᵥ v) = _
  rw [dotProduct_mulVec, vecMul_mulVec]
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp R.property.1]
  simp

theorem rotate_dot_pull (R : SO3) (q v : Vec3) : q ⬝ᵥ rotate R v = rotate R⁻¹ q ⬝ᵥ v := by
  have h := rotate_dot R (rotate R⁻¹ q) v
  simpa [← rotate_mul] using h

namespace Gravity

def field3 (μ : ℝ) (q : Vec3) : Vec3 := WithLp.ofLp (field μ (WithLp.toLp 2 q : Jacobian.E3))
def gradient3 (μ : ℝ) (q v : Vec3) : Vec3 :=
  WithLp.ofLp (gradient μ (WithLp.toLp 2 q : Jacobian.E3) (WithLp.toLp 2 v))
def remainder3 (μ : ℝ) (q v : Vec3) : Vec3 := field3 μ (q+v)-field3 μ q-gradient3 μ q v

theorem remainder3_bound (μ : ℝ) (hμ : 0 ≤ μ) (q v : Vec3) (hd : enorm v < enorm q) :
    enorm (remainder3 μ q v) ≤ remainderBound μ (enorm q) (enorm v) :=
  remainder_bound μ hμ (WithLp.toLp 2 q : Jacobian.E3) (WithLp.toLp 2 v) hd

/-- The actual gradient expressed in the reference frame, equation (16). -/
theorem gradient3_body (μ : ℝ) (R : SO3) (q v : Vec3) (hq : 0 < enorm q) :
    rotate R⁻¹ (gradient3 μ q (rotate R v)) =
      radialMap (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) v := by
  change rotate R⁻¹ ((3*μ*inner ℝ (WithLp.toLp 2 q : Jacobian.E3)
    (WithLp.toLp 2 (rotate R v))/enorm q^5) • q - (μ/enorm q^3) • rotate R v) = _
  rw [inner_toLp, rotate_sub, rotate_smul, rotate_smul, ← rotate_mul]
  simp only [inv_mul_cancel, rotate_one, rotate_dot_pull, radialMap,
    Jacobian.unitAxis, rotate_enorm, smul_dotProduct, smul_eq_mul, dotProduct_smul]
  match_scalars <;> field_simp

def bodyGravity (μ : ℝ) (R : SO3) (q k : Vec3) (t : ℝ) (p : Vec3) : Vec3 :=
  Jacobian.leftInv k t (rotate R⁻¹
    (field3 μ (q+physicalImpulse R (t • k) p)-field3 μ q))

def higherGravity (μ : ℝ) (R : SO3) (q k : Vec3) (t : ℝ) (p : Vec3) : Vec3 :=
  Jacobian.leftInv k t (rotate R⁻¹ (remainder3 μ q (physicalImpulse R (t • k) p)))

theorem gravity_decomposition (μ : ℝ) (R : SO3) (q k p : Vec3)
    (hq : 0 < enorm q) (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) :
    bodyGravity μ R q k t p =
      radialMap (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) p +
      attitudeResidual (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) k t p +
      higherGravity μ R q k t p := by
  have hj : physicalImpulse R (t • k) p = rotate R (Jacobian.left k t p) := by
    rw [physicalImpulse, Jacobian.leftAt_axis k p hk t ht]
  have he : field3 μ (q+physicalImpulse R (t • k) p)-field3 μ q =
      gradient3 μ q (physicalImpulse R (t • k) p) +
        remainder3 μ q (physicalImpulse R (t • k) p) := by unfold remainder3; abel
  rw [bodyGravity, he, rotate_add, hj,
    gradient3_body μ R q (Jacobian.left k t p) hq]
  simp only [Jacobian.leftInv, Jacobian.planeMap, Axis.axial, Axis.transverse,
    dotProduct_add, map_add, add_smul, smul_add]
  unfold attitudeResidual higherGravity
  rw [hj]
  simp only [Jacobian.leftInv, Jacobian.planeMap, Axis.axial, Axis.transverse,
    dotProduct_add, map_add, add_smul, smul_add]
  module

/-- Equation (26), using the physical separation d and the proven vector
Taylor remainder, with no conditional Hessian or norm hypotheses. -/
theorem higherGravity_bound (μ : ℝ) (hμ : 0 ≤ μ) (R : SO3) (q k p : Vec3)
    (hk : k ⬝ᵥ k = 1) (t : ℝ) (ht : 0 < t) (htπ : t < π)
    (hd : enorm (physicalImpulse R (t • k) p) < enorm q) :
    enorm (higherGravity μ R q k t p) ≤ ((t/2)/sin (t/2))*
      remainderBound μ (enorm q) (enorm (physicalImpulse R (t • k) p)) := by
  have hb := remainder3_bound μ hμ q (physicalImpulse R (t • k) p) hd
  have hs : 0 < sin (t/2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  unfold higherGravity
  calc
    _ ≤ _ := Jacobian.leftInv_bound k _ hk t ht (by linarith [pi_pos])
    _ ≤ _ := by
      rw [rotate_enorm]
      exact mul_le_mul_of_nonneg_left hb (by positivity)

end Gravity
end GNC
