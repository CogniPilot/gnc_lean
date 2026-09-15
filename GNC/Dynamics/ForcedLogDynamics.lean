import GNC.Dynamics.MatrixDynamics

/-! Proposition 2 assembled from the physical trajectories and the checked
gravity and control decompositions. The only coordinate hypothesis is a
differentiable log lift of the actual group error. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem physical_separation (chief deputy : SE23) (x : LogState)
    (he : SE23.error chief deputy = groupExp x) :
    deputy.pos = chief.pos + physicalImpulse chief.rot (x 2) (x 0) := by
  have h := congrArg (fun X : SE23 => rotate chief.rot X.pos) he
  simp only [SE23.error_pos, groupExp, ← rotate_mul, mul_inv_cancel, rotate_one] at h
  change deputy.pos-chief.pos = physicalImpulse chief.rot (x 2) (x 0) at h
  rw [← h]; abel

theorem blockInverse_add (x y z : LogState) (hqπ : enorm (x 2) < 2*π) :
    Jacobian.blockInverse x (y+z) = Jacobian.blockInverse x y + Jacobian.blockInverse x z := by
  have h : Jacobian.blockLeft x (Jacobian.blockInverse x (y+z)) =
      Jacobian.blockLeft x (Jacobian.blockInverse x y+Jacobian.blockInverse x z) := by
    rw [blockLeft_add]
    simp only [Jacobian.blockLeft_inverse_all _ _ hqπ]
  have hi := congrArg (Jacobian.blockInverse x) h
  simpa only [Jacobian.blockInverse_left_all _ _ hqπ] using hi

theorem velocityOnly_add (v w : Vec3) : velocityOnly (v+w) = velocityOnly v+velocityOnly w := by
  ext i j; fin_cases i <;> simp [velocityOnly]

theorem controlInput_sub (a w abar wbar : Vec3) :
    Jacobian.controlInput a w-Jacobian.controlInput abar wbar =
      Jacobian.controlInput (a-abar) (w-wbar) := by
  ext i j; fin_cases i <;> simp [Jacobian.controlInput]

/-- Equation (72), as an action on the position, velocity and attitude blocks. -/
def forcedLinear (μ : ℝ) (R : SO3) (q a w abar wbar : Vec3) (x : LogState) : LogState :=
  ![x 1-((1/2:ℝ) • (w+wbar)) ⨯₃ x 0,
    Gravity.radialMap (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) (x 0) -
      ((1/2:ℝ) • (w+wbar)) ⨯₃ x 1 - ((1/2:ℝ) • (a+abar)) ⨯₃ x 2,
    -((1/2:ℝ) • (w+wbar)) ⨯₃ x 2]

theorem forcedLinear_mean (μ : ℝ) (R : SO3) (q a w abar wbar : Vec3) (x : LogState) :
    forcedLinear μ R q a w abar wbar x =
      logDrift ((1/2:ℝ) • (Jacobian.controlInput a w+Jacobian.controlInput abar wbar)) x +
      velocityOnly (Gravity.radialMap (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) (x 0)) := by
  ext i j
  fin_cases i <;> simp [forcedLinear, logDrift, ad, Jacobian.controlInput, velocityOnly] <;> ring

/-- The attitude block of the retained linear system is autonomous. -/
theorem forcedLinear_attitude (μ : ℝ) (R : SO3) (q a w abar wbar : Vec3) (x : LogState) :
    forcedLinear μ R q a w abar wbar x 2 = -((1/2:ℝ) • (w+wbar)) ⨯₃ x 2 := rfl

/-- Equation (71), including the actual inverse-square gravity evaluated
at the spacecraft positions. No decomposition identity is assumed. -/
theorem spacecraft_forced_log_equation {X Y : ℝ → SE23} {x : ℝ → LogState}
    {dx : LogState} {a w abar wbar : Vec3} {μ t : ℝ}
    (hX : HasDerivAt (fun s => SE23.toMatrix (X s))
      (spacecraftDerivative (X t) (Jacobian.controlInput a w) (Gravity.field3 μ (X t).pos)) t)
    (hY : HasDerivAt (fun s => SE23.toMatrix (Y s))
      (spacecraftDerivative (Y t) (Jacobian.controlInput abar wbar) (Gravity.field3 μ (Y t).pos)) t)
    (hx : HasDerivAt x dx t) (he : ∀ s, SE23.error (Y s) (X s) = groupExp (x s))
    (hq : 0 < enorm (Y t).pos) (hθ : 0 < enorm (x t 2)) (hθπ : enorm (x t 2) < π) :
    dx = forcedLinear μ (Y t).rot (Y t).pos a w abar wbar (x t) +
      Jacobian.controlInput (a-abar) (w-wbar) + Jacobian.controlResidual (x t) (a-abar) (w-wbar) +
      velocityOnly (Gravity.attitudeResidual (μ/enorm (Y t).pos^3)
        (Jacobian.unitAxis (rotate (Y t).rot⁻¹ (Y t).pos))
        (Jacobian.unitAxis (x t 2)) (enorm (x t 2)) (x t 0)) +
      velocityOnly (Gravity.higherGravity μ (Y t).rot (Y t).pos
        (Jacobian.unitAxis (x t 2)) (enorm (x t 2)) (x t 0)) := by
  have h := spacecraft_log_equation hX hY hx he hθπ
  rw [blockInverse_add _ _ _ (by linarith [pi_pos]), controlInput_sub,
    Jacobian.control_decomposition, Jacobian.blockInverse_velocityOnly] at h
  have hg := Gravity.gravity_decomposition μ (Y t).rot (Y t).pos
    (Jacobian.unitAxis (x t 2)) (x t 0) hq (Jacobian.unitAxis_unit _ hθ) (enorm (x t 2)) hθ
  have hgi : Jacobian.inverseAt (x t 2)
      (rotate (Y t).rot⁻¹ (Gravity.field3 μ (X t).pos-Gravity.field3 μ (Y t).pos)) =
      Gravity.bodyGravity μ (Y t).rot (Y t).pos
        (Jacobian.unitAxis (x t 2)) (enorm (x t 2)) (x t 0) := by
    rw [physical_separation (Y t) (X t) (x t) (he t)]
    unfold Gravity.bodyGravity
    rw [Jacobian.unitAxis_reconstruct _ hθ]
    exact Jacobian.inverseAt_eq (x t 2) _ hθ
  rw [hgi, hg, velocityOnly_add, velocityOnly_add] at h
  rw [h, forcedLinear_mean]
  have hm := mean_input_ad (Jacobian.controlInput a w) (Jacobian.controlInput abar wbar) (x t)
  rw [controlInput_sub] at hm
  unfold logDrift
  linear_combination (norm := module) hm

end GNC
