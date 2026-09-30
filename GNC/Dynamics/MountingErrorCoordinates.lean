import GNC.Dynamics.LieGravityPullback
import GNC.Dynamics.LieErrorReconstruction

/-! A constant thruster mounting error is not a matched-body-rate attitude
error. Pulling back its rotating-frame translation error makes the thrust
term linear in the mounting rotation vector, but conjugates the frame
transport by the SO(3) Jacobian. Gravity and that transport must remain in
any physical certificate. The hypotheses below are the rotating-frame
position/velocity ODE; no numerical solution or error bound is assumed. -/
noncomputable section
namespace GNC.MountingErrorCoordinates
open Matrix Real

def transport (φ ω x : Vec3) : Vec3 :=
  Jacobian.inverseAt φ (ω ⨯₃ Jacobian.leftAt φ x)

theorem equations (φ : Vec3) (hφ : enorm φ < 2*π)
    {d v : ℝ → Vec3} {ω g a : Vec3} {t : ℝ}
    (hd : HasDerivAt d (-(ω ⨯₃ d t)+v t) t)
    (hv : HasDerivAt v
      (-(ω ⨯₃ v t)+g+(rotate (rotationExp φ) a-a)) t) :
    HasDerivAt (fun s => Jacobian.inverseAt φ (d s))
      (-transport φ ω (Jacobian.inverseAt φ (d t))+
        Jacobian.inverseAt φ (v t)) t ∧
    HasDerivAt (fun s => Jacobian.inverseAt φ (v s))
      (-transport φ ω (Jacobian.inverseAt φ (v t))+
        Jacobian.inverseAt φ g+φ ⨯₃ a) t := by
  have hneg (x : Vec3) : Jacobian.inverseAt φ (-x) = -Jacobian.inverseAt φ x := by
    simp only [Jacobian.inverseAt, map_neg]
    module
  constructor
  · convert inverseAt_fixed_derivative φ hd using 1
    simp only [transport,Jacobian.leftAt_inverseAt_all φ _ hφ,
      Jacobian.inverseAt_add,hneg]
  · convert inverseAt_fixed_derivative φ hv using 1
    simp only [transport,Jacobian.leftAt_inverseAt_all φ _ hφ,
      Jacobian.inverseAt_add,hneg,inverseAt_thrust φ a hφ]

/-- Reconstruction does not amplify a translation-coordinate error when
the same mounting angle is used for the truth and the predictor. -/
theorem output_error (φ ρ ρhat : Vec3) (hφ : enorm φ < 2*π) :
    enorm (Jacobian.leftAt φ ρ-Jacobian.leftAt φ ρhat) ≤ enorm (ρ-ρhat) := by
  rw [←Jacobian.leftAt_sub]
  exact leftAt_nonexpansive φ (ρ-ρhat) hφ

end GNC.MountingErrorCoordinates
