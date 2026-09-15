import GNC.Control.PointingAngle
import GNC.Lie.PrincipalDomain

/-! From a log-attitude certificate to a physical three-dimensional thrust
direction. The rotation axis is unrestricted. -/
noncomputable section
open Matrix Real
namespace GNC.ThrustSupport

theorem rotation_axis_pairing (k n : Vec3) {θ : ℝ}
    (hk : k ⬝ᵥ k = 1) (hn : n ⬝ᵥ n = 1) (hθ : 0 < θ) :
    n ⬝ᵥ rotate (rotationExp (θ • k)) n = cos θ+(1-cos θ)*(k ⬝ᵥ n)^2 := by
  rw [rotate, Cayley.rotationExp_axis k hk θ hθ]
  simp only [add_mulVec, one_mulVec, smul_mulVec, pow_two, ← mulVec_mulVec,
    skew_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, hn,
    dot_cross_self, mul_zero, add_zero]
  simp only [cross_cross_eq_smul_sub_smul', dotProduct_sub, dotProduct_smul,
    smul_eq_mul, hk, hn, dotProduct_comm n k]
  ring

/-- The logarithm's norm bounds the deviation of every physical unit vector.
This makes a log-attitude bound usable by the thrust support certificate. -/
theorem rotationExp_cap (q n : Vec3) (hn : n ⬝ᵥ n = 1) :
    rotate (rotationExp q) n ∈ Cap n (cos (enorm q)) := by
  constructor
  · rw [dot_self_lengthSq, ← enorm_sq, rotate_enorm, enorm_sq, ← dot_self_lengthSq, hn]
  · by_cases hq : q = 0
    · simpa [hq, rotationExp, skew_zero, rotate, hn] using cos_le_one (enorm (0 : Vec3))
    · have hpos : 0 < enorm q := lt_of_le_of_ne (enorm_nonneg q)
        (Ne.symm (mt (enorm_eq_zero_iff q).mp hq))
      have h := rotation_axis_pairing (Jacobian.unitAxis q) n
        (Jacobian.unitAxis_unit q hpos) hn hpos
      rw [Jacobian.unitAxis_reconstruct q hpos] at h
      rw [h]
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (cos_le_one _)) (sq_nonneg _))

theorem rotationExp_cap_of_bound (q n : Vec3) {α : ℝ}
    (hn : n ⬝ᵥ n = 1) (hq : enorm q ≤ α) (hπ : α ≤ π) :
    rotate (rotationExp q) n ∈ Cap n (cos α) := by
  have h := rotationExp_cap q n hn
  refine ⟨h.1, ?_⟩
  exact (cos_le_cos_of_nonneg_of_le_pi (enorm_nonneg q) hπ hq).trans h.2

end GNC.ThrustSupport
