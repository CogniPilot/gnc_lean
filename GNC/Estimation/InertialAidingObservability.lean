import GNC.Lie.Euclidean
import Mathlib.Tactic

noncomputable section
namespace GNC.Estimation.InertialAidingObservability
open Matrix

def gpsDeniedOutput (position velocity field : Vec3) (rotation : Matrix (Fin 3) (Fin 3) ℝ)
    (groundHeight : ℝ) : (Fin 2 → ℝ) × ℝ × Vec3 :=
  let height := position 2 - groundHeight
  let bodyVelocity := rotationᵀ *ᵥ velocity
  (![-bodyVelocity 1 / height, bodyVelocity 0 / height],
    height, rotationᵀ *ᵥ field)

theorem horizontal_translation_unobservable (position velocity field shift : Vec3)
    (rotation : Matrix (Fin 3) (Fin 3) ℝ) (groundHeight : ℝ) (horizontal : shift 2 = 0) :
    gpsDeniedOutput (position + shift) velocity field rotation groundHeight =
      gpsDeniedOutput position velocity field rotation groundHeight := by
  simp [gpsDeniedOutput, Pi.add_apply, horizontal]

theorem prediction_preserves_translation (position velocity acceleration shift : Vec3)
    (dt : ℝ) :
    position + shift + dt • velocity + (dt^2 / 2) • acceleration =
      (position + dt • velocity + (dt^2 / 2) • acceleration) + shift := by
  module

theorem gps_observes_translation (position shift : Vec3) (nonzero : shift ≠ 0) :
    position + shift ≠ position := by
  intro same
  apply nonzero
  exact add_left_cancel (show position + shift = position + 0 by simpa using same)

end GNC.Estimation.InertialAidingObservability
