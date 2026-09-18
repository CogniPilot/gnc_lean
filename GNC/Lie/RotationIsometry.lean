import GNC.Lie.Euclidean
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! The SO(3) action as a Euclidean linear isometry, so exact coordinate
changes preserve physical error norms and commute with time derivatives. -/
noncomputable section
namespace GNC

def rotationIsometry (R : SO3) : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := WithLp.toLp 2 (rotate R v.ofLp)
  invFun v := WithLp.toLp 2 (rotate R⁻¹ v.ofLp)
  left_inv v := by
    change WithLp.toLp 2 (rotate R⁻¹ (rotate R v.ofLp))=v
    rw [←rotate_mul,inv_mul_cancel,rotate_one]
  right_inv v := by
    change WithLp.toLp 2 (rotate R (rotate R⁻¹ v.ofLp))=v
    rw [←rotate_mul,mul_inv_cancel,rotate_one]
  map_add' u v := by
    change WithLp.toLp 2 (rotate R (u.ofLp+v.ofLp))=_
    rw [rotate_add]
    rfl
  map_smul' c v := by
    change WithLp.toLp 2 (rotate R (c • v.ofLp))=_
    simp only [rotate,Matrix.mulVec_smul,WithLp.toLp_smul,RingHom.id_apply]
  norm_map' v := rotate_enorm R v.ofLp

theorem rotation_isometry_derivative (R : SO3) {f : ℝ → EuclideanSpace ℝ (Fin 3)}
    {v : EuclideanSpace ℝ (Fin 3)} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => rotationIsometry R (f s)) (rotationIsometry R v) t :=
  (rotationIsometry R).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

end GNC
