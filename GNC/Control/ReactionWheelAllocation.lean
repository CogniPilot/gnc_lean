import GNC.Dynamics.ReactionWheels
import GNC.Control.LogBackstepping

/-! Exact ideal motor allocation for the existing body-torque backstepping
law. Motor saturation, estimation and actuator dynamics require additional
bounds; this identity does not assert robust tracking under those effects. -/
noncomputable section
set_option autoImplicit false
namespace GNC.ReactionWheelAllocation
open Matrix ReactionWheels
open scoped Matrix

theorem backstepping_realizes (J : InertiaMatrix) (I : Vec3 ≃ₗ[ℝ] Vec3)
    (hJ : ∀ v, J *ᵥ v = I v) (w h L desiredDerivative rateError correction : Vec3)
    (k : ℝ) :
    I.symm (L-motorForBodyTorque w h
      (LogBackstepping.torqueCommand I w desiredDerivative rateError correction k) L-
      w ⨯₃ bodyMomentum J w h) = desiredDerivative-k • rateError-correction := by
  rw [allocation_identity, hJ]
  exact LogBackstepping.torqueCommand_realizes I w desiredDerivative rateError correction k

end GNC.ReactionWheelAllocation
