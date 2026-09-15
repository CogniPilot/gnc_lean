import GNC.Dynamics.MixedErrorDynamics
import GNC.Analysis.SmallAngle

/-! Exact half-angle direction change of the transverse impulse in Lemma 5. -/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC

theorem rotationExp_transverse (k v : Vec3) (hk : k ⬝ᵥ k = 1) (hv : k ⬝ᵥ v = 0)
    (t : ℝ) (ht : 0 < t) :
    rotate (rotationExp (t • k)) v = cos t • v + sin t • (k ⨯₃ v) := by
  rw [rotate, rotationExp_axis k hk t ht]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, pow_two,
    ← mulVec_mulVec, skew_mulVec, Axis.cross_sq k v hk, Axis.axial, hv, zero_smul, zero_sub]
  module

/-- On the transverse plane the true impulse map is exactly a positive
contraction followed by a rotation through half the attitude error. -/
theorem impulse_half_angle (R : SO3) (k v : Vec3) (hk : k ⬝ᵥ k = 1) (hv : k ⬝ᵥ v = 0)
    (t : ℝ) (ht : 0 < t) :
    physicalImpulse R (t • k) v = Jacobian.contraction t •
      rotate R (rotate (rotationExp ((t/2) • k)) v) := by
  rw [physicalImpulse, Jacobian.leftAt_axis k v hk t ht,
    rotationExp_transverse k v hk hv (t/2) (by linarith), ← rotate_smul]
  congr 1
  simp only [Jacobian.left, Jacobian.planeMap, Axis.transverse, Axis.axial, hv,
    zero_smul, sub_zero, zero_add, Jacobian.contraction, smul_add, smul_smul,
    Jacobian.half_sin t, Jacobian.half_cos t]
  match_scalars <;> field_simp <;> ring

theorem impulse_transverse_magnitude (R : SO3) (k v : Vec3)
    (hk : k ⬝ᵥ k = 1) (hv : k ⬝ᵥ v = 0) (t : ℝ) (ht : 0 < t) (htπ : t < 2*π) :
    enorm (physicalImpulse R (t • k) v) = Jacobian.contraction t*enorm v := by
  rw [impulse_half_angle R k v hk hv t ht, enorm_smul, rotate_enorm, rotate_enorm,
    abs_of_pos (Jacobian.contraction_pos t ht htπ)]

theorem contraction_eq_sinc (t : ℝ) (ht : t ≠ 0) : Jacobian.contraction t = sinc (t/2) := by
  rw [sinc_of_ne_zero (div_ne_zero ht (by norm_num))]
  unfold Jacobian.contraction
  field_simp

end GNC
