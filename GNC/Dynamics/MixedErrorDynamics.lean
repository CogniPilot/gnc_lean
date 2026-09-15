import GNC.Lie.RightJacobian
import GNC.Dynamics.RigidBodyKinematics

/-! The paper's right-adjoint gravity notation and exact deputy-body impulse
conversion, connected to the physical trajectories. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem deputy_of_error (chief deputy : SE23) (x : LogState)
    (he : SE23.error chief deputy = groupExp x) : deputy = chief*groupExp x := by
  rw [← he, SE23.error, mul_inv_cancel_left]

/-- Lemma 1, in exactly the right-Jacobian/deputy-frame convention of (13). -/
theorem gravity_right_velocity (deputy : SE23) (x : LogState) (g : Vec3) :
    Jacobian.blockRightInverse x (adjoint deputy⁻¹ (velocityOnly g)) =
      velocityOnly (Jacobian.inverseAt (-x 2) (rotate deputy.rot⁻¹ g)) := by
  rw [adjoint_velocityOnly, Jacobian.blockRightInverse_velocityOnly]
  rfl

theorem gravity_right_transport (chief deputy : SE23) (x : LogState) (g : Vec3)
    (he : SE23.error chief deputy = groupExp x) (hθ : enorm (x 2) < 2*π) :
    Jacobian.blockRightInverse x (adjoint deputy⁻¹ (velocityOnly g)) =
      Jacobian.blockInverse x (velocityOnly (rotate chief.rot⁻¹ g)) := by
  rw [deputy_of_error chief deputy x he, _root_.mul_inv_rev, adjoint_mul,
    inverse_right_adjoint _ _ hθ, adjoint_velocityOnly]
  rfl

/-- Proposition 1, equation (11), directly from the component equations (4).
It includes θ=0. A differentiable principal log lift remains explicit. -/
theorem proposition1 {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx : LogState} {a w abar wbar g gbar : Vec3} {t : ℝ}
    (hX : SpacecraftODEAt X a w g t) (hY : SpacecraftODEAt Y abar wbar gbar t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s) = groupExp (x s))
    (hθπ : enorm (x t 2) < π) :
    dx = logDrift (Jacobian.controlInput a w) (x t) +
      Jacobian.blockInverse (x t) (Jacobian.controlInput (a-abar) (w-wbar)) +
      Jacobian.blockRightInverse (x t) (adjoint (X t)⁻¹ (velocityOnly (g-gbar))) := by
  rw [gravity_right_transport (Y t) (X t) (x t) (g-gbar) (he t) (by linarith [pi_pos])]
  have h := physical_log_equation hX hY hx he hθπ
  rw [blockInverse_add _ _ _ (by linarith [pi_pos])] at h
  exact h.trans (add_assoc _ _ _).symm

/-- Proposition 2, with the physical component equations as hypotheses. -/
theorem proposition2 {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx : LogState} {a w abar wbar : Vec3} {μ t : ℝ}
    (hX : SpacecraftODEAt X a w (Gravity.field3 μ (X t).pos) t)
    (hY : SpacecraftODEAt Y abar wbar (Gravity.field3 μ (Y t).pos) t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s) = groupExp (x s))
    (hq : 0 < enorm (Y t).pos) (hθ : 0 < enorm (x t 2)) (hθπ : enorm (x t 2) < π) :
    dx = forcedLinear μ (Y t).rot (Y t).pos a w abar wbar (x t) +
      Jacobian.controlInput (a-abar) (w-wbar) + Jacobian.controlResidual (x t) (a-abar) (w-wbar) +
      velocityOnly (Gravity.attitudeResidual (μ/enorm (Y t).pos^3)
        (Jacobian.unitAxis (rotate (Y t).rot⁻¹ (Y t).pos))
        (Jacobian.unitAxis (x t 2)) (enorm (x t 2)) (x t 0)) +
      velocityOnly (Gravity.higherGravity μ (Y t).rot (Y t).pos
        (Jacobian.unitAxis (x t 2)) (enorm (x t 2)) (x t 0)) :=
  spacecraft_forced_log_equation
    ((spacecraft_ode_iff _ _ _ _ _).mp hX) ((spacecraft_ode_iff _ _ _ _ _).mp hY) hx he hq hθ hθπ

/-- Theorem 1's exact decomposition now starts with the paper's named
right-adjoint gravity term and the actual physical separation. -/
theorem gravity_right_decomposition (μ : ℝ) (chief deputy : SE23) (x : LogState)
    (he : SE23.error chief deputy = groupExp x)
    (hq : 0 < enorm chief.pos) (hθ : 0 < enorm (x 2)) (hθπ : enorm (x 2) < π) :
    Jacobian.blockRightInverse x
      (adjoint deputy⁻¹ (velocityOnly (Gravity.field3 μ deputy.pos-Gravity.field3 μ chief.pos))) =
    velocityOnly (Gravity.radialMap (μ/enorm chief.pos^3)
      (Jacobian.unitAxis (rotate chief.rot⁻¹ chief.pos)) (x 0)) +
    velocityOnly (Gravity.attitudeResidual (μ/enorm chief.pos^3)
      (Jacobian.unitAxis (rotate chief.rot⁻¹ chief.pos))
      (Jacobian.unitAxis (x 2)) (enorm (x 2)) (x 0)) +
    velocityOnly (Gravity.higherGravity μ chief.rot chief.pos
      (Jacobian.unitAxis (x 2)) (enorm (x 2)) (x 0)) := by
  rw [gravity_right_transport chief deputy x _ he (by linarith [pi_pos]),
    Jacobian.blockInverse_velocityOnly]
  have hg := Gravity.gravity_decomposition μ chief.rot chief.pos
    (Jacobian.unitAxis (x 2)) (x 0) hq (Jacobian.unitAxis_unit _ hθ) (enorm (x 2)) hθ
  have hgi : Jacobian.inverseAt (x 2)
      (rotate chief.rot⁻¹ (Gravity.field3 μ deputy.pos-Gravity.field3 μ chief.pos)) =
      Gravity.bodyGravity μ chief.rot chief.pos
        (Jacobian.unitAxis (x 2)) (enorm (x 2)) (x 0) := by
    rw [physical_separation chief deputy x he]
    unfold Gravity.bodyGravity
    rw [Jacobian.unitAxis_reconstruct _ hθ]
    exact Jacobian.inverseAt_eq (x 2) _ hθ
  rw [hgi, hg, velocityOnly_add, velocityOnly_add]

theorem left_right_rotation (x : LogState) (v : Vec3) :
    Jacobian.leftAt (x 2) v = rotate (rotationExp (x 2)) (Jacobian.leftAt (-x 2) v) := by
  have h := congrArg (fun z : LogState => z 1) (left_right_adjoint x (velocityOnly v))
  simpa [Jacobian.blockRight, Jacobian.blockLeft, velocityOnly, adjoint, groupExp] using h

/-- Lemma 5's exact second formula in (82), in the deputy body frame. -/
theorem deputy_body_impulse (chief deputy : SE23) (x : LogState) (dv : Vec3)
    (he : SE23.error chief deputy = groupExp x) :
    rotate deputy.rot⁻¹ (physicalImpulse chief.rot (x 2) dv) = Jacobian.leftAt (-x 2) dv := by
  have hr : deputy.rot = chief.rot*rotationExp (x 2) := by
    rw [deputy_of_error chief deputy x he]; rfl
  rw [physicalImpulse, left_right_rotation x dv,
    ← rotate_mul chief.rot (rotationExp (x 2)), ← hr, ← rotate_mul]
  simp

end GNC
