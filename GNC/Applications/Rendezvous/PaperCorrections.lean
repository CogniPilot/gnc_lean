import GNC.Lie.ControlResidual

/-! Counterexamples to overstrong implications in Corollaries 2 and 4.
They concern the algebraic input conditions, not a numerical trajectory. -/
noncomputable section
open Matrix
open scoped Matrix
namespace GNC

/-- Zero mean thrust does not imply both vehicles coast. -/
theorem zero_mean_noncoasting : ∃ a abar : Vec3,
    a ≠ 0 ∧ abar ≠ 0 ∧ (1/2:ℝ) • (a+abar) = 0 := by
  refine ⟨![1,0,0], ![-1,0,0], ?_, ?_, ?_⟩
  · intro h; have h0 := congrFun h 0; norm_num at h0
  · intro h; have h0 := congrFun h 0; norm_num at h0
  · ext i; fin_cases i <;> norm_num

/-- Even two coasting vehicles can have a nonzero angular mismatch.
Coasting therefore does not force a pure-velocity input mismatch. -/
theorem coasting_angular_mismatch : ∃ w wbar : Vec3,
    w ≠ wbar ∧ Jacobian.controlInput (0:Vec3) w-Jacobian.controlInput 0 wbar ≠
      velocityOnly 0 := by
  refine ⟨![0,0,1],0,?_,?_⟩
  · intro h; have h2 := congrFun h (2 : Fin 3)
    change (1:ℝ) = 0 at h2
    norm_num at h2
  · intro h; have h22 := congrFun (congrFun h (2 : Fin 3)) (2 : Fin 3)
    change (1:ℝ)-0 = 0 at h22
    norm_num at h22

end GNC
