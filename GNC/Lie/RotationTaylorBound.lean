import GNC.Lie.RotationKinematics
import GNC.Lie.ExponentialCoordinates
import GNC.Analysis.TaylorCertificate
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! A sharp-order vector Taylor bound for the Cartesian angle STM.
The second derivative is a rotated double cross product. Its norm is
bounded before integration, so the comparator pays theta^2/2, without
separate and unnecessarily loose sine and cosine triangle bounds. -/
noncomputable section
namespace GNC.RotationTaylorBound
open Matrix
open scoped Matrix Matrix.Norms.Operator

def curve (φ v : Vec3) (s : ℝ) : Jacobian.E3 :=
  WithLp.toLp 2 (rotate (rotationExp (s • φ)) v)

theorem derivative (φ v : Vec3) (s : ℝ) :
    HasDerivAt (curve φ v) (curve φ (φ ⨯₃ v) s) s := by
  have hR : HasDerivAt (fun t => (rotationExp (t • φ)).val)
      ((rotationExp (s • φ)).val*skew φ) s := by
    simpa only [rotationExp, skew_smul] using hasDerivAt_exp_smul_const (skew φ) s
  have hv := SymplecticResponse.mulVec_derivative hR (hasDerivAt_const s v)
  have he : HasDerivAt (fun t => rotate (rotationExp (t • φ)) v)
      (rotate (rotationExp (s • φ)) (φ ⨯₃ v)) s := by
    simpa only [rotate, mulVec_zero, zero_add, add_zero, ←mulVec_mulVec, skew_mulVec] using hv
  exact (WithLp.linearEquiv 2 ℝ Vec3).symm.toLinearMap.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s he

theorem bound (φ v : Vec3) :
    enorm (rotate (rotationExp φ) v-v-φ ⨯₃ v)≤enorm φ^2/2*enorm v := by
  have hn := (cross_enorm_le φ (φ ⨯₃ v)).trans
    (mul_le_mul_of_nonneg_left (cross_enorm_le φ v) (enorm_nonneg φ))
  have h := TaylorCertificate.remainder_bound (curve φ v)
    (curve φ (φ ⨯₃ v)) (curve φ (φ ⨯₃ (φ ⨯₃ v)))
    (fun t _ => derivative φ v t) (fun t _ => derivative φ (φ ⨯₃ v) t)
    (continuous_iff_continuousAt.mpr (fun t =>
      (derivative φ (φ ⨯₃ (φ ⨯₃ v)) t).continuousAt)).continuousOn
    (fun t _ => show ‖curve φ (φ ⨯₃ (φ ⨯₃ v)) t‖≤enorm φ^2*enorm v from by
      change enorm (rotate _ _)≤_
      rw [rotate_enorm]
      convert hn using 1 <;> ring)
  have hzero (w : Vec3) : curve φ w 0=WithLp.toLp 2 w := by
    simp [curve, rotationExp, rotate, skew_zero]
  rw [hzero, hzero] at h
  change enorm (rotate (rotationExp (1 • φ)) v-v-φ ⨯₃ v)≤_ at h
  simpa only [one_smul, mul_div_right_comm] using h

end GNC.RotationTaylorBound
