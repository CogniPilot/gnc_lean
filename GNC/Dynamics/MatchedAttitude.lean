import GNC.Magnus.MagnusFlow
import GNC.Lie.RotationKinematics
import GNC.Lie.CayleyChart

/-! Matched body-rate histories preserve a constant inertial attitude offset.
The angular rate may change both magnitude and axis. This is a cancellation
between two actual solutions, not termination of the nominal Magnus series.
Unequal body-rate histories have the explicit nonzero relative derivative.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.MatchedAttitude
open Matrix
open scoped Matrix.Norms.Operator

theorem same_body_rate (R H : ℝ → SO3) (ω : ℝ → Vec3)
    (hω : Continuous ω)
    (hR : ∀ t, HasDerivAt (fun s => (R s).val) ((R t).val*skew (ω t)) t)
    (hH : ∀ t, HasDerivAt (fun s => (H s).val) ((H t).val*skew (ω t)) t)
    (E : SO3) (h0 : R 0=E*H 0) : ∀ t, R t=E*H t := by
  have he := Magnus.mixed_flow_unique (fun _ => (0 : Cayley.Mat3))
    (fun t => skew (ω t)) continuous_const (Cayley.contDiff_skew.continuous.comp hω)
    (fun t => (R t).val) (fun t => E.val*(H t).val)
    (fun t => by simpa only [zero_mul,zero_add] using hR t)
    (fun t => by
      convert (hH t).const_mul E.val using 1
      simp only [zero_mul,zero_add,mul_assoc])
    (congrArg Subtype.val h0)
  intro t
  exact Subtype.ext (congrFun he t)

/-- The inertial relative rotation is fixed even for noncommuting angular
rate generators at different times. -/
theorem relative_constant (R H : ℝ → SO3) (ω : ℝ → Vec3)
    (hω : Continuous ω)
    (hR : ∀ t, HasDerivAt (fun s => (R s).val) ((R t).val*skew (ω t)) t)
    (hH : ∀ t, HasDerivAt (fun s => (H s).val) ((H t).val*skew (ω t)) t) :
    ∀ t, R t*(H t)⁻¹=R 0*(H 0)⁻¹ := by
  have he := same_body_rate R H ω hω hR hH (R 0*(H 0)⁻¹) (by simp)
  intro t
  rw [he t]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Arbitrary body acceleration histories inherit the same fixed rotation
parameter. Time integration and gravity approximation remain separate. -/
theorem thrust_difference (R H : ℝ → SO3) (ω a : ℝ → Vec3)
    (hω : Continuous ω)
    (hR : ∀ t, HasDerivAt (fun s => (R s).val) ((R t).val*skew (ω t)) t)
    (hH : ∀ t, HasDerivAt (fun s => (H s).val) ((H t).val*skew (ω t)) t)
    (E : SO3) (h0 : R 0=E*H 0) (t : ℝ) :
    rotate (R t) (a t)-rotate (H t) (a t)=
      rotate E (rotate (H t) (a t))-rotate (H t) (a t) := by
  rw [same_body_rate R H ω hω hR hH E h0 t,rotate_mul]

/-- Angular-rate mismatch is a distinct input. It cannot be represented
by a constant initial attitude offset without additional hypotheses. -/
theorem relative_derivative {R H : ℝ → SO3} {ω ωbar : Vec3} {t : ℝ}
    (hR : HasDerivAt (fun s => (R s).val) ((R t).val*skew ω) t)
    (hH : HasDerivAt (fun s => (H s).val) ((H t).val*skew ωbar) t) :
    HasDerivAt (fun s => (R s).val*((H s)⁻¹).val)
      ((R t).val*(skew ω-skew ωbar)*((H t)⁻¹).val) t := by
  convert hR.mul (RotationKinematics.inverse_derivative hH) using 1
  noncomm_ring

/-- Roll about the initial thrust axis is invisible to that direction but
affects a later, nonparallel force. This holds for arbitrarily small angles. -/
theorem roll_transfer (θ : ℝ) :
    rotate (AxisRotation.zRotation θ) ![0,0,1]=![0,0,1] ∧
    rotate (AxisRotation.zRotation θ) ![1,0,0]=![Real.cos θ,Real.sin θ,0] := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [rotate,AxisRotation.zRotation,AxisRotation.zMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end GNC.MatchedAttitude
