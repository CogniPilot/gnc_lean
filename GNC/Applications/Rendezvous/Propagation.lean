import GNC.Applications.Rendezvous.ODEPlanner
import GNC.Analysis.Transition

/-! Propagation of the structural decoupling in (72). The vanishing transfer
blocks are consequences of the ODE, not hypotheses on the planner. -/
noncomputable section
open Matrix
namespace GNC

namespace ForcedResponse
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A constant symmetry of the generator is a symmetry of its propagator. -/
theorem propagate_commutation (Φ : ℝ → (End (V := V))ˣ) (A : ℝ → End (V := V))
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) (A t*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (P : End (V := V))
    (hc : ∀ t v, P (A t v) = A t (P v)) (t : ℝ) (v : V) :
    P ((Φ t).val v) = (Φ t).val (P v) := by
  let f : ℝ → V := fun s => P ((Φ s).val v)
  have hf (s : ℝ) : HasDerivAt f (A s (f s)+0) s := by
    have h := (hΦ s).clm_apply (hasDerivAt_const s v)
    convert P.hasFDerivAt.comp_hasDerivAt s h using 1
    simp only [ContinuousLinearMap.mul_apply, map_zero, add_zero, hc, f]
  have h := congrFun (response_unique Φ A hΦ h₀ (fun _ => 0) continuous_const f hf) t
  simpa [f, h₀, matched_forcing] using h

end ForcedResponse

/-- The linear operator in (72), with the actual gravitational gradient. -/
def forcedLinearMap (μ : ℝ) (R : SO3) (q a w abar wbar : Vec3) : LogState →ₗ[ℝ] LogState where
  toFun := forcedLinear μ R q a w abar wbar
  map_add' x y := by
    funext i
    fin_cases i <;>
      simp [forcedLinear, Gravity.radialMap, dotProduct_add, smul_add, add_smul] <;> module
  map_smul' c x := by
    funext i
    fin_cases i <;>
      simp [forcedLinear, Gravity.radialMap, smul_sub, smul_smul] <;> module

def forcedOperator (μ : ℝ) (R : SO3) (q a w abar wbar : Vec3) : ODEPlanner.End :=
  (forcedLinearMap μ R q a w abar wbar).toContinuousLinearMap

def translationProjection : ODEPlanner.End :=
  ({ toFun := fun x : LogState => ![x 0,x 1,0]
     map_add' := by intros; ext i j; fin_cases i <;> simp
     map_smul' := by intros; ext i j; fin_cases i <;> simp } : LogState →ₗ[ℝ] LogState).toContinuousLinearMap

theorem translationProjection_apply (x : LogState) : translationProjection x = ![x 0,x 1,0] := rfl

theorem forcedOperator_apply (μ : ℝ) (R : SO3) (q a w abar wbar : Vec3) (x : LogState) :
    forcedOperator μ R q a w abar wbar x = forcedLinear μ R q a w abar wbar x := rfl

theorem zero_mean_commutation (μ : ℝ) (R : SO3) (q a w abar wbar : Vec3)
    (ha : a+abar = 0) (x : LogState) :
    translationProjection (forcedOperator μ R q a w abar wbar x) =
      forcedOperator μ R q a w abar wbar (translationProjection x) := by
  change (![_,_,0] : LogState) = forcedLinear μ R q a w abar wbar ![x 0,x 1,0]
  ext i j; fin_cases i <;> simp [forcedOperator, forcedLinearMap, forcedLinear, ha]

/-- Corollary 2 under zero mean thrust: both attitude-to-translation blocks
vanish. Opposite nonzero thrusts also satisfy this hypothesis. -/
theorem zero_mean_transfer_blocks (Φ : ℝ → ODEPlanner.Endˣ)
    (μ : ℝ) (R : ℝ → SO3) (q a w abar wbar : ℝ → Vec3)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val)
      (forcedOperator μ (R t) (q t) (a t) (w t) (abar t) (wbar t)*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (ha : ∀ t, a t+abar t = 0) (t : ℝ) :
    ODEPlanner.block (Φ t).val 0 2 = 0 ∧ ODEPlanner.block (Φ t).val 1 2 = 0 := by
  have h (v : Vec3) := ForcedResponse.propagate_commutation Φ _ hΦ h₀ translationProjection
    (fun s x => zero_mean_commutation μ (R s) (q s) (a s) (w s) (abar s) (wbar s) (ha s) x)
    t (Pi.single 2 v)
  have hz (v : Vec3) : translationProjection (Pi.single 2 v) = 0 := by
    ext i j; fin_cases i <;> simp [translationProjection_apply]
  constructor
  · apply LinearMap.ext
    intro v
    funext j
    have hh := congrArg (fun x : LogState => x 0 j) (h v)
    simpa [hz, translationProjection_apply, ODEPlanner.block] using hh
  · apply LinearMap.ext
    intro v
    funext j
    have hh := congrArg (fun x : LogState => x 1 j) (h v)
    simpa [hz, translationProjection_apply, ODEPlanner.block] using hh

/-- The two log impulses are independent of the initial attitude once the
two coupling blocks vanish. The physical R·J conversion still uses attitude. -/
theorem decoupled_impulses (F : Planner.Transfer Vec3) (hpR : F.pR = 0) (hvR : F.vR = 0)
    (p v r s : Vec3) :
    F.departure p v r = F.departure p v s ∧ F.arrival p v r = F.arrival p v s := by
  constructor
  · simp [Planner.Transfer.departure, hpR]
  · simp [Planner.Transfer.arrival, F.arrival_velocity, hpR, hvR]

theorem zero_mean_planner (Φ : ℝ → ODEPlanner.Endˣ)
    (μ : ℝ) (R : ℝ → SO3) (q a w abar wbar : ℝ → Vec3)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val)
      (forcedOperator μ (R t) (q t) (a t) (w t) (abar t) (wbar t)*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (ha : ∀ t, a t+abar t = 0)
    (u : ℝ → LogState) (t : ℝ) (pv : Vec3 ≃ₗ[ℝ] Vec3) (p v r s : Vec3) :
    (ODEPlanner.transfer Φ u t pv).departure p v r =
      (ODEPlanner.transfer Φ u t pv).departure p v s ∧
    (ODEPlanner.transfer Φ u t pv).arrival p v r =
      (ODEPlanner.transfer Φ u t pv).arrival p v s := by
  obtain ⟨hp,hv⟩ := zero_mean_transfer_blocks Φ μ R q a w abar wbar hΦ h₀ ha t
  exact decoupled_impulses _ hp hv p v r s

/-- Corollary 1, equation (90), for blocks extracted from the propagator. -/
theorem matched_departure (Φ : ℝ → ODEPlanner.Endˣ) (t : ℝ)
    (pv : Vec3 ≃ₗ[ℝ] Vec3) (p v r : Vec3) :
    (ODEPlanner.transfer Φ (fun _ => 0) t pv).departure p v r =
      -v-pv.symm (ODEPlanner.block (Φ t).val 0 0 p+ODEPlanner.block (Φ t).val 0 2 r) := by
  simp [ODEPlanner.transfer, Planner.Transfer.departure, ForcedResponse.matched_forcing]

theorem matched_operator (μ : ℝ) (R : SO3) (q a w : Vec3) (x : LogState) :
    forcedOperator μ R q a w a w x = logDrift (Jacobian.controlInput a w) x+
      velocityOnly (Gravity.radialMap (μ/enorm q^3) (Jacobian.unitAxis (rotate R⁻¹ q)) (x 0)) := by
  rw [forcedOperator_apply, forcedLinear_mean]
  congr 2
  ext i j; fin_cases i <;> simp [Jacobian.controlInput] <;> ring

theorem matched_control_residual (x : LogState) : Jacobian.controlResidual x 0 0 = 0 := by
  ext i j; fin_cases i <;>
    simp [Jacobian.controlResidual, Jacobian.M, Jacobian.diagonalRemainder]

/-- The constant-angle conclusion of Corollary 1 in the actual Euclidean norm. -/
theorem matched_attitude_enorm (w r : ℝ → Vec3)
    (hr : ∀ t, HasDerivAt r (-(w t ⨯₃ r t)) t) (t t₀ : ℝ) :
    enorm (r t) = enorm (r t₀) := by
  have h := attitude_lengthSq_constant w r (fun s i => (hasDerivAt_pi.mp (hr s)) i) t t₀
  rw [← enorm_sq, ← enorm_sq] at h
  nlinarith [enorm_nonneg (r t), enorm_nonneg (r t₀)]

/-- Corrected Corollary 4 requires matched angular rates as well as a
coasting deputy. Both mean inputs and the forcing are then reference data. -/
theorem coasting_deputy_matched_rates (abar wbar : Vec3) :
    Jacobian.controlInput ((0:Vec3)-abar) (wbar-wbar) = velocityOnly (-abar) ∧
    (1/2:ℝ) • ((0:Vec3)+abar) = (1/2:ℝ) • abar ∧
    (1/2:ℝ) • (wbar+wbar) = wbar := by
  refine ⟨?_, by simp, ?_⟩
  · ext i j; fin_cases i <;> simp [Jacobian.controlInput, velocityOnly]
  · ext j; simp; ring

/-- Equation (79): the autonomous attitude row gives two zero blocks in
the actual transition operator, even when mean thrust is nonzero. -/
theorem attitude_transfer_blocks (Φ : ℝ → ODEPlanner.Endˣ)
    (μ : ℝ) (R : ℝ → SO3) (q a w abar wbar : ℝ → Vec3)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val)
      (forcedOperator μ (R t) (q t) (a t) (w t) (abar t) (wbar t)*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (t : ℝ) :
    ODEPlanner.block (Φ t).val 2 0 = 0 ∧ ODEPlanner.block (Φ t).val 2 1 = 0 := by
  have hz (j : Fin 3) (hj : j ≠ 2) (v : Vec3) : (Φ t).val (Pi.single j v) 2 = 0 := by
    let r : ℝ → Vec3 := fun s => (Φ s).val (Pi.single j v) 2
    have hd (s : ℝ) : HasDerivAt r (-(((1/2:ℝ) • (w s+wbar s)) ⨯₃ r s)) s := by
      have h := (hΦ s).clm_apply (hasDerivAt_const s (Pi.single j v))
      have h2 := hasDerivAt_pi.mp h (2 : Fin 3)
      simpa [r, ContinuousLinearMap.mul_apply, forcedOperator_apply, forcedLinear] using h2
    apply zero_attitude_invariant (fun s => (1/2:ℝ) • (w s+wbar s)) r
      (fun s i => (hasDerivAt_pi.mp (hd s)) i) 0 _ t
    simp [r, h₀, Pi.single_eq_of_ne hj.symm]
  constructor
  · apply LinearMap.ext
    intro v
    simpa [ODEPlanner.block] using hz 0 (by decide) v
  · apply LinearMap.ext
    intro v
    simpa [ODEPlanner.block] using hz 1 (by decide) v

/-- The complete affine attitude response (79) contains neither initial
translation nor the departure impulse. -/
theorem attitude_response (Φ : ℝ → ODEPlanner.Endˣ)
    (μ : ℝ) (R : ℝ → SO3) (q a w abar wbar : ℝ → Vec3)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val)
      (forcedOperator μ (R t) (q t) (a t) (w t) (abar t) (wbar t)*(Φ t).val) t)
    (h₀ : Φ 0 = 1) (u : ℝ → LogState) (t : ℝ) (p v r : Vec3) :
    ForcedResponse.response Φ u ![p,v,r] t 2 =
      ODEPlanner.block (Φ t).val 2 2 r+ForcedResponse.response Φ u 0 t 2 := by
  obtain ⟨hp,hv⟩ := attitude_transfer_blocks Φ μ R q a w abar wbar hΦ h₀ t
  rw [ForcedResponse.response_affine]
  simp [ODEPlanner.block_action, hp, hv]

end GNC
