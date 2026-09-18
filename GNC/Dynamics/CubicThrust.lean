import GNC.Dynamics.CartesianRadiusDefect
import GNC.Dynamics.LieRadiusQuadratic

/-! A cubic Cartesian thrust approximation with a rotation-invariant tail.
Bounding the vector remainder before expanding monomials avoids charging
the same finite-angle structure separately along each coordinate. -/
noncomputable section
namespace GNC.CubicThrust
open Matrix Real

theorem error (φ b bhat : Vec3) {σ δ B : ℝ}
    (hφ : enorm φ<2*π) (hσ : enorm φ≤σ)
    (hδ : enorm (b-bhat)≤δ) (hB : enorm bhat≤B) :
    enorm ((rotate (rotationExp φ) b-b)-
      LieRadiusQuadratic.apply φ (φ ⨯₃ bhat))≤
      σ*δ+LieRadiusQuadratic.tail σ*σ*B := by
  have hσ0 := (enorm_nonneg φ).trans hσ
  rw [←leftAt_cross_rotation]
  have he : Jacobian.leftAt φ (φ ⨯₃ b)-LieRadiusQuadratic.apply φ (φ ⨯₃ bhat)=
      Jacobian.leftAt φ (φ ⨯₃ (b-bhat))+
        (Jacobian.leftAt φ (φ ⨯₃ bhat)-LieRadiusQuadratic.apply φ (φ ⨯₃ bhat)) := by
    simp only [map_sub,Jacobian.leftAt_sub]
    module
  rw [he]
  apply (enorm_add_le _ _).trans
  apply add_le_add
  · exact (leftAt_nonexpansive φ _ hφ).trans
      ((cross_enorm_le _ _).trans (mul_le_mul hσ hδ (enorm_nonneg _) hσ0))
  · apply (LieRadiusQuadratic.error_bound φ (φ ⨯₃ bhat)).trans
    have hc := (cross_enorm_le φ bhat).trans
      (mul_le_mul hσ hB (enorm_nonneg _) hσ0)
    have ht := LieRadiusQuadratic.tail_mono (enorm_nonneg φ) hσ
    calc
      _≤LieRadiusQuadratic.tail σ*(σ*B) :=
        mul_le_mul ht hc (enorm_nonneg _) (LieRadiusQuadratic.tail_nonnegative hσ0)
      _=_ := by ring

end GNC.CubicThrust
