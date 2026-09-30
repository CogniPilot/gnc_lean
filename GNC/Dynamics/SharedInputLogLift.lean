import GNC.Dynamics.MatchedAttitude
import GNC.Dynamics.RigidBodyKinematics
import GNC.Dynamics.LieGravityPullback
import GNC.Dynamics.LieRadiusCertificate

/-! Construct the logarithmic error of shared-input physical trajectories.

Equal body angular rates preserve an inertial rotation offset. Consequently
the moving reference-body logarithm can be built from a fixed inverse
Jacobian followed by a rotation. This construction includes zero attitude
error and requires neither an assumed log lift nor a derivative of a
singular axis-angle quotient. Gravity may differ between the trajectories.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.SharedInputLogLift
open Matrix Real
open scoped Matrix Matrix.Norms.Operator

/-- Rotation equivariance of the actual matrix exponential. -/
theorem rotation_exp_conjugation (R : SO3) (φ : Vec3) :
    rotationExp (rotate R φ) = R * rotationExp φ * R⁻¹ := by
  let U : (Matrix (Fin 3) (Fin 3) ℝ)ˣ :=
    ⟨R.val, (R⁻¹).val, congrArg Subtype.val (mul_inv_cancel R),
      congrArg Subtype.val (inv_mul_cancel R)⟩
  have hs : skew (rotate R φ) = R.val * skew φ * (R⁻¹).val := by
    have h := congrArg (fun A => A * (R⁻¹).val) (skew_rotate R φ)
    have hcancel : R.val * (R⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel R)
    simpa only [mul_assoc, hcancel, mul_one] using h
  apply Subtype.ext
  change NormedSpace.exp (skew (rotate R φ)) =
    R.val * NormedSpace.exp (skew φ) * (R⁻¹).val
  rw [hs]
  exact NormedSpace.exp_units_conj U (skew φ)

/-- Explicit left-error coordinates, using a fixed inertial rotation vector. -/
def coordinates (φ : Vec3) (X Y : SE23) : LogState :=
  ![rotate Y.rot⁻¹ (Jacobian.inverseAt φ (X.pos-Y.pos)),
    rotate Y.rot⁻¹ (Jacobian.inverseAt φ (X.vel-Y.vel)), rotate Y.rot⁻¹ φ]

theorem angle_norm (φ : Vec3) (X Y : SE23) :
    enorm (coordinates φ X Y 2) = enorm φ := rotate_enorm _ _

/-- Exact reconstruction, with no restriction on translation error. -/
theorem reconstruction (φ : Vec3) (X Y : SE23) (hφ : enorm φ < 2*π)
    (hR : X.rot = rotationExp φ * Y.rot) :
    SE23.error Y X = groupExp (coordinates φ X Y) := by
  apply SE23.ext
  · change Y.rot⁻¹ * X.rot = rotationExp (rotate Y.rot⁻¹ φ)
    rw [hR, rotation_exp_conjugation]
    simp only [inv_inv, mul_assoc]
  · change (SE23.error Y X).vel =
      Jacobian.leftAt (rotate Y.rot⁻¹ φ)
        (rotate Y.rot⁻¹ (Jacobian.inverseAt φ (X.vel-Y.vel)))
    rw [SE23.error_vel, leftAt_rotation_equivariant,
      Jacobian.leftAt_inverseAt_all φ _ hφ]
  · change (SE23.error Y X).pos =
      Jacobian.leftAt (rotate Y.rot⁻¹ φ)
        (rotate Y.rot⁻¹ (Jacobian.inverseAt φ (X.pos-Y.pos)))
    rw [SE23.error_pos, leftAt_rotation_equivariant,
      Jacobian.leftAt_inverseAt_all φ _ hφ]

/-- The constructed lift is the unique principal log, not merely a choice
of exponential preimage. No bound on position or velocity is needed. -/
theorem unique_coordinates (φ : Vec3) (X Y : SE23) (hφ : enorm φ < π)
    (hR : X.rot = rotationExp φ * Y.rot) (x : LogState)
    (hx : enorm (x 2) < π) (he : SE23.error Y X = groupExp x) :
    x = coordinates φ X Y := by
  apply groupExp_injective hx (by simpa only [angle_norm] using hφ)
  exact he.symm.trans (reconstruction φ X Y (by linarith [pi_pos]) hR)

/-- Derivative computed directly from the physical component equations. -/
def rate (φ : Vec3) (X Y : SE23) (a ω g h : Vec3) : LogState :=
  ![coordinates φ X Y 1 - ω ⨯₃ coordinates φ X Y 0,
    rotate Y.rot⁻¹ (Jacobian.inverseAt φ
      ((rotate X.rot a+g)-(rotate Y.rot a+h))) - ω ⨯₃ coordinates φ X Y 1,
    -(ω ⨯₃ coordinates φ X Y 2)]

theorem derivative (φ : Vec3) {X Y : ℝ → SE23} {a ω g h : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a ω g t) (hY : SpacecraftODEAt Y a ω h t) :
    HasDerivAt (fun s => coordinates φ (X s) (Y s))
      (rate φ (X t) (Y t) a ω g h) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact RotationKinematics.inverse_rotate_derivative hY.2.2
      (inverseAt_fixed_derivative φ (hX.1.sub hY.1))
  · exact RotationKinematics.inverse_rotate_derivative hY.2.2
      (inverseAt_fixed_derivative φ (hX.2.1.sub hY.2.1))
  · simpa only [rotate_zero, zero_sub] using
      RotationKinematics.inverse_rotate_derivative hY.2.2 (hasDerivAt_const t φ)

private theorem continuous_cross {f g : ℝ → Vec3}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun t => f t ⨯₃ g t) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [cross_apply] <;> fun_prop

private theorem continuous_inverse (φ : Vec3) {f : ℝ → Vec3}
    (hf : Continuous f) : Continuous (fun t => Jacobian.inverseAt φ (f t)) := by
  exact (hf.sub ((continuous_cross continuous_const hf).const_smul _)).add
    ((continuous_cross continuous_const (continuous_cross continuous_const hf)).const_smul _)

/-- The lift and its derivative are continuous consequences of ordinary
physical kinematics and continuous accelerations. No chart regularity oracle. -/
theorem exists_lift (X Y : ℝ → SE23) (a ω g h : ℝ → Vec3)
    (ha : Continuous a) (hω : Continuous ω) (hg : Continuous g) (hh : Continuous h)
    (hX : ∀ t, SpacecraftODEAt X (a t) (ω t) (g t) t)
    (hY : ∀ t, SpacecraftODEAt Y (a t) (ω t) (h t) t)
    (φ : Vec3) (hφ : enorm φ < π)
    (h0 : (X 0).rot = rotationExp φ * (Y 0).rot) :
    ∃ x dx : ℝ → LogState,
      Continuous x ∧ Continuous dx ∧
      (∀ t, HasDerivAt x (dx t) t) ∧
      (∀ t, SE23.error (Y t) (X t) = groupExp (x t)) ∧
      (∀ t, enorm (x t 2) = enorm φ) ∧
      (∀ t, x t = coordinates φ (X t) (Y t)) := by
  let x := fun t => coordinates φ (X t) (Y t)
  let dx := fun t => rate φ (X t) (Y t) (a t) (ω t) (g t) (h t)
  have hd : ∀ t, HasDerivAt x (dx t) t := fun t => derivative φ (hX t) (hY t)
  have hx : Continuous x := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hXR : Continuous (fun t => (X t).rot.val) :=
    continuous_iff_continuousAt.mpr fun t => (hX t).2.2.continuousAt
  have hYR : Continuous (fun t => (Y t).rot.val) :=
    continuous_iff_continuousAt.mpr fun t => (hY t).2.2.continuousAt
  have hxc (i : Fin 3) : Continuous (fun t => x t i) := (continuous_apply i).comp hx
  have hdx : Continuous dx := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (hxc 1).sub (continuous_cross hω (hxc 0))
    · exact (hYR.matrix_transpose.matrix_mulVec (continuous_inverse φ
        (((hXR.matrix_mulVec ha).add hg).sub ((hYR.matrix_mulVec ha).add hh)))).sub
          (continuous_cross hω (hxc 1))
    · exact (continuous_cross hω (hxc 2)).neg
  have hrot := MatchedAttitude.same_body_rate (fun t => (X t).rot)
    (fun t => (Y t).rot) ω hω (fun t => (hX t).2.2) (fun t => (hY t).2.2)
    (rotationExp φ) h0
  exact ⟨x, dx, hx, hdx, hd,
    fun t => reconstruction φ (X t) (Y t) (by linarith [pi_pos]) (hrot t),
    fun t => angle_norm φ (X t) (Y t), fun _ => rfl⟩

end GNC.SharedInputLogLift
