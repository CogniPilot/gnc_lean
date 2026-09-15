import GNC.Analysis.FundamentalSolution
import GNC.Applications.Rendezvous.Propagation
import GNC.Lie.SE23Manifold

/-! The constructed fundamental solution applies to the actual spacecraft
operator (72), and supplies an existing rendezvous trajectory in Proposition 3. -/
noncomputable section
open Matrix
namespace GNC

theorem forcedOperator_continuous (μ : ℝ) (R : ℝ → SO3) (q a w abar wbar : ℝ → Vec3)
    (hR : Continuous R) (hq : Continuous q) (ha : Continuous a) (hw : Continuous w)
    (habar : Continuous abar) (hwbar : Continuous wbar) (hq0 : ∀ t, 0 < enorm (q t)) :
    Continuous (fun t => forcedOperator μ (R t) (q t) (a t) (w t) (abar t) (wbar t)) := by
  have hrot : Continuous (fun t => rotate (R t)⁻¹ (q t)) :=
    (SE23.matrixAction.continuous.comp (continuous_subtype_val.comp hR.inv)).clm_apply hq
  have haxis : Continuous (fun t => Jacobian.unitAxis (rotate (R t)⁻¹ (q t))) :=
    ((enorm_continuous.comp hrot).inv₀ (fun t => by
      simpa only [Function.comp_apply, rotate_enorm] using (hq0 t).ne')).smul hrot
  have hcoef : Continuous (fun t => μ/enorm (q t)^3) :=
    continuous_const.div ((enorm_continuous.comp hq).pow 3)
      (fun t => pow_ne_zero 3 (hq0 t).ne')
  rw [continuous_clm_apply]
  intro v
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [forcedOperator_apply, forcedLinear, Gravity.radialMap, cross_apply,
      dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
  all_goals fun_prop

theorem spacecraft_fundamental_exists (μ : ℝ) (R : ℝ → SO3) (q a w abar wbar : ℝ → Vec3)
    (hR : Continuous R) (hq : Continuous q) (ha : Continuous a) (hw : Continuous w)
    (habar : Continuous abar) (hwbar : Continuous wbar) (hq0 : ∀ t, 0 < enorm (q t)) :
    ∃ Φ : ℝ → ODEPlanner.Endˣ, Φ 0 = 1 ∧ ∀ t,
      HasDerivAt (fun s => (Φ s).val)
        (forcedOperator μ (R t) (q t) (a t) (w t) (abar t) (wbar t)*(Φ t).val) t :=
  ForcedResponse.exists_fundamental _ (forcedOperator_continuous μ R q a w abar wbar hR hq ha hw habar hwbar hq0)

namespace ODEPlanner

def plannedTransfer (A : ℝ → End) (hA : Continuous A) (u : ℝ → LogState)
    (T : ℝ) (pv : Vec3 ≃ₗ[ℝ] Vec3) : Planner.Transfer Vec3 :=
  transfer (ForcedResponse.fundamental A hA) u T pv

/-- Proposition 3 now supplies the trajectory as well as the impulse pair.
The remaining invertibility condition is the paper's actual pv block. -/
theorem exists_planned_trajectory (A : ℝ → End) (hA : Continuous A)
    (u : ℝ → LogState) (hu : Continuous u) (T : ℝ) (pv : Vec3 ≃ₗ[ℝ] Vec3)
    (hpv : ∀ v, pv v = block (ForcedResponse.fundamental A hA T).val 0 1 v) (p v r : Vec3) :
    ∃ f : ℝ → LogState,
      f 0 = ![p,v+(plannedTransfer A hA u T pv).departure p v r,r] ∧
      (∀ t, HasDerivAt f (A t (f t)+u t) t) ∧
      f T 0 = 0 ∧ f T 1+(plannedTransfer A hA u T pv).arrival p v r = 0 := by
  obtain ⟨f,hf,-⟩ := ForcedResponse.exists_unique_response A hA u hu
    ![p,v+(plannedTransfer A hA u T pv).departure p v r,r]
  refine ⟨f,hf.1,hf.2,?_⟩
  exact rendezvous _ A (ForcedResponse.fundamental_derivative A hA)
    (ForcedResponse.fundamental_initial A hA) u hu T pv hpv p v r f hf.2 hf.1

theorem planned_pair_unique (A : ℝ → End) (hA : Continuous A)
    (u : ℝ → LogState) (hu : Continuous u) (T : ℝ) (pv : Vec3 ≃ₗ[ℝ] Vec3)
    (hpv : ∀ v, pv v = block (ForcedResponse.fundamental A hA T).val 0 1 v)
    (p v r d₀ dT : Vec3) (f : ℝ → LogState)
    (hf : ∀ t, HasDerivAt f (A t (f t)+u t) t) (hi : f 0 = ![p,v+d₀,r])
    (hp : f T 0 = 0) (hv : f T 1+dT = 0) :
    d₀ = (plannedTransfer A hA u T pv).departure p v r ∧
    dT = (plannedTransfer A hA u T pv).arrival p v r :=
  unique_pair _ A (ForcedResponse.fundamental_derivative A hA)
    (ForcedResponse.fundamental_initial A hA) u hu T pv hpv p v r d₀ dT f hf hi hp hv

end ODEPlanner
end GNC
