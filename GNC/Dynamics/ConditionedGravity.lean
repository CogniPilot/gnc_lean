import GNC.Dynamics.PrincipalErrorDynamics

/-! Retain the gravity--attitude commutator when the attitude history is known.
The resulting generator is conditioned on that history. It is not one
state-independent STM simultaneously valid for every initial attitude error.
The only remaining gravity residual is the actual quadratic Taylor remainder. -/
noncomputable section
open Matrix Real
namespace GNC
namespace Gravity

def conditionedGradient (μ : ℝ) (R : SO3) (q k : Vec3) (θ : ℝ) (p : Vec3) : Vec3 :=
  Jacobian.leftInv k θ (radialMap (μ/enorm q^3)
    (Jacobian.unitAxis (rotate R⁻¹ q)) (Jacobian.left k θ p))

/-- For a fixed attitude parameter, the retained gravity map is linear. -/
def conditionedGradientMap (μ : ℝ) (R : SO3) (q k : Vec3) (θ : ℝ) : Vec3 →ₗ[ℝ] Vec3 where
  toFun := conditionedGradient μ R q k θ
  map_add' u v := by
    have hi (u v : Vec3) : Jacobian.leftInv k θ (u+v) =
        Jacobian.leftInv k θ u + Jacobian.leftInv k θ v :=
      congrArg WithLp.ofLp ((Jacobian.leftInvCLM k θ).map_add
        (WithLp.toLp 2 u) (WithLp.toLp 2 v))
    simp only [conditionedGradient, Jacobian.left_add]
    have hg (l : ℝ) (r u v : Vec3) : radialMap l r (u+v) =
        radialMap l r u + radialMap l r v := by
      simp [radialMap, dotProduct_add, add_smul, smul_add]
      module
    rw [hg, hi]
  map_smul' c v := by
    have hi (u : Vec3) : Jacobian.leftInv k θ (c • u) = c • Jacobian.leftInv k θ u :=
      congrArg WithLp.ofLp ((Jacobian.leftInvCLM k θ).map_smul c (WithLp.toLp 2 u))
    simp only [conditionedGradient, Jacobian.left_smul, RingHom.id_apply]
    have hg (l : ℝ) (r u : Vec3) : radialMap l r (c • u) = c • radialMap l r u := by
      simp [radialMap, dotProduct_smul, smul_sub, smul_smul]
      module
    rw [hg, hi]

theorem conditioned_decomposition (μ : ℝ) (R : SO3) (q k p : Vec3)
    (hq : 0 < enorm q) (hk : k ⬝ᵥ k = 1) (θ : ℝ) (hθ : 0 < θ) :
    bodyGravity μ R q k θ p = conditionedGradient μ R q k θ p +
      higherGravity μ R q k θ p := by
  rw [gravity_decomposition μ R q k p hq hk θ hθ]
  unfold attitudeResidual conditionedGradient
  abel

theorem conditioned_remainder_bound (μ : ℝ) (hμ : 0 ≤ μ) (R : SO3) (q k p : Vec3)
    (hq : 0 < enorm q) (hk : k ⬝ᵥ k = 1) (θ : ℝ) (hθ : 0 < θ) (hπ : θ < π)
    (hd : enorm (physicalImpulse R (θ • k) p) < enorm q) :
    enorm (bodyGravity μ R q k θ p - conditionedGradient μ R q k θ p) ≤
      ((θ/2)/sin (θ/2))*remainderBound μ (enorm q)
        (enorm (physicalImpulse R (θ • k) p)) := by
  rw [conditioned_decomposition μ R q k p hq hk θ hθ, add_sub_cancel_left]
  exact higherGravity_bound μ hμ R q k p hk θ hθ hπ hd

end Gravity

def conditionedLinear (μ : ℝ) (R : SO3) (q a w k : Vec3) (θ : ℝ) (x : LogState) : LogState :=
  ![x 1-w ⨯₃ x 0,
    Gravity.conditionedGradient μ R q k θ (x 0)-w ⨯₃ x 1-a ⨯₃ x 2,
    -w ⨯₃ x 2]

theorem absorb_attitudeResidual (μ : ℝ) (R : SO3) (q a w k : Vec3) (θ : ℝ) (x : LogState) :
    forcedLinear μ R q a w a w x +
      velocityOnly (Gravity.attitudeResidual (μ/enorm q^3)
        (Jacobian.unitAxis (rotate R⁻¹ q)) k θ (x 0)) =
      conditionedLinear μ R q a w k θ x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [forcedLinear, conditionedLinear, velocityOnly,
    Gravity.conditionedGradient, Gravity.attitudeResidual, smul_add, cross_apply,
    Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Actual physical trajectories imply the conditioned principal log equation.
The angular history is still supplied by the independent attitude block. -/
theorem principal_conditioned_equation {X Y : ℝ → SE23} {a w : Vec3} {μ t : ℝ}
    (hX : SpacecraftODEAt X a w (Gravity.field3 μ (X t).pos) t)
    (hY : SpacecraftODEAt Y a w (Gravity.field3 μ (Y t).pos) t)
    (hd : ∀ s, SE23.error (Y s) (X s) ∈ PrincipalLog.domain)
    (hq : 0 < enorm (Y t).pos) (hθ : 0 < enorm (principalError X Y t 2)) :
    deriv (principalError X Y) t =
      conditionedLinear μ (Y t).rot (Y t).pos a w
        (Jacobian.unitAxis (principalError X Y t 2)) (enorm (principalError X Y t 2))
        (principalError X Y t) +
      velocityOnly (Gravity.higherGravity μ (Y t).rot (Y t).pos
        (Jacobian.unitAxis (principalError X Y t 2)) (enorm (principalError X Y t 2))
        (principalError X Y t 0)) := by
  rw [principal_proposition2 hX hY hd hq hθ]
  simp only [sub_self]
  have hc : Jacobian.controlInput (0 : Vec3) 0 = 0 := by ext i j; fin_cases i <;> rfl
  have hr : Jacobian.controlResidual (principalError X Y t) 0 0 = 0 := by
    simp [Jacobian.controlResidual, Jacobian.diagonalRemainder, Jacobian.M]
  rw [hc, hr, add_zero, add_zero, absorb_attitudeResidual]

end GNC
