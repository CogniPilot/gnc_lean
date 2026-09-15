import GNC.Control.ThrustSupport
import Mathlib.Analysis.ODE.Gronwall

/-! When adding attitude states cannot improve the physical fuel optimum.
The nonlinear translation field, constraints and cost must factor through
the reduced problem, and every feasible reduced plan must admit a full
realization. No linearization, minimum attainment or particular Lie group
is assumed by the attainable-cost theorem. -/
noncomputable section
open Set Matrix
namespace GNC.DecoupledPlanning

def attainable {P C : Type*} (feasible : P → Prop) (observe : P → C) : Set C :=
  {c | ∃ p, feasible p ∧ observe p = c}

/-- A cost/observation-preserving projection with feasible realizations
preserves the entire attainable set, including when it is empty. The
observation may be fuel, terminal state, or their ordered pair. -/
theorem attainable_projection {Full Reduced C : Type*}
    (project : Full → Reduced) (full : Full → Prop) (reduced : Reduced → Prop)
    (observe : Reduced → C)
    (hproject : ∀ p, full p → reduced (project p))
    (hlift : ∀ u, reduced u → ∃ p, full p ∧ project p = u) :
    attainable full (observe ∘ project) = attainable reduced observe := by
  ext c
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨project p, hproject p hp, he⟩
  · rintro ⟨u, hu, he⟩
    obtain ⟨p, hp, hpu⟩ := hlift u hu
    exact ⟨p, hp, by simpa only [Function.comp_apply, hpu] using he⟩

/-- Every fuel budget is feasible in one model exactly when it is feasible
in the other. In particular, infeasibility and all infimum/optimum values
coincide without needing to assume that an optimum exists. -/
theorem budget_iff {Full Reduced : Type*}
    (project : Full → Reduced) (full : Full → Prop) (reduced : Reduced → Prop)
    (cost : Reduced → ℝ)
    (hproject : ∀ p, full p → reduced (project p))
    (hlift : ∀ u, reduced u → ∃ p, full p ∧ project p = u) (budget : ℝ) :
    (∃ p, full p ∧ cost (project p) ≤ budget) ↔
    ∃ u, reduced u ∧ cost u ≤ budget := by
  constructor
  · rintro ⟨p, hp, hc⟩
    exact ⟨project p, hproject p hp, hc⟩
  · rintro ⟨u, hu, hc⟩
    obtain ⟨p, hp, he⟩ := hlift u hu
    exact ⟨p, hp, by simpa only [he] using hc⟩

/-- Pointwise realization of an inertial acceleration by ideal unconstrained
three-axis body thrust. Slew, direction and power constraints would need
additional hypotheses to turn this into a realizable vehicle trajectory. -/
theorem inertial_command_realization (R : SO3) (u : Vec3) :
    rotate R (R.valᵀ *ᵥ u) = u ∧ enorm (R.valᵀ *ᵥ u) = enorm u := by
  have hR : R.val * R.valᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp R.property.1
  have he : rotate R (R.valᵀ *ᵥ u) = u := by
    change R.val *ᵥ (R.valᵀ *ᵥ u) = u
    rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  refine ⟨he, ?_⟩
  exact (rotate_enorm R (R.valᵀ *ᵥ u)).symm.trans (congrArg enorm he)

section Dynamics
variable {E Att U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete translation field factors through position/velocity/input,
independently of the attitude argument. This includes every perturbing force,
not merely the nominal thrust term. -/
def decoupled (F : ℝ → E → Att → U → E) (f : ℝ → E → U → E) : Prop :=
  ∀ t z R u, F t z R u = f t z u

/-- Same inertial input and translational initial condition imply identical
nonlinear translations for arbitrary attitude histories. Mathlib supplies
ODE uniqueness on the common Lipschitz region; no local linear model is used.
Right derivatives permit application on closed forward time intervals. -/
theorem trajectory_independent
    (F : ℝ → E → Att → U → E) (f : ℝ → E → U → E) (hF : decoupled F f)
    (u : ℝ → U) (R S : ℝ → Att) (x y : ℝ → E) (region : ℝ → Set E)
    {a b : ℝ} (K : NNReal)
    (hlip : ∀ t ∈ Ico a b, LipschitzOnWith K (fun z => f t z (u t)) (region t))
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hdx : ∀ t ∈ Ico a b, HasDerivWithinAt x (F t (x t) (R t) (u t)) (Ici t) t)
    (hdy : ∀ t ∈ Ico a b, HasDerivWithinAt y (F t (y t) (S t) (u t)) (Ici t) t)
    (hrx : ∀ t ∈ Ico a b, x t ∈ region t)
    (hry : ∀ t ∈ Ico a b, y t ∈ region t) (hinit : x a = y a) :
    EqOn x y (Icc a b) := by
  apply ODE_solution_unique_of_mem_Icc_right hlip hx ?_ hrx hy ?_ hry hinit
  · intro t ht
    simpa only [hF t (x t) (R t) (u t)] using hdx t ht
  · intro t ht
    simpa only [hF t (y t) (S t) (u t)] using hdy t ht
end Dynamics

section Terminal
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- Even if attitude changes the full state, it may be invisible to the
specified terminal output. The exact condition is annihilation of every
admissible direction difference by the observed burn kernel. -/
theorem terminal_eq_nominal (K : ι → Vec3 →ₗ[ℝ] V) (u : ι → ℝ) (q n : ι → Vec3)
    (hnull : ∀ j, K j (q j-n j) = 0) :
    (∑ j, u j • K j (q j)) = ∑ j, u j • K j (n j) := by
  apply Finset.sum_congr rfl
  intro j _
  have he : K j (q j) = K j (n j) := sub_eq_zero.mp (by simpa only [map_sub] using hnull j)
  rw [he]

/-- Under the null-coupling condition the robust terminal requirement is
exactly the nominal requirement. Nominal membership prevents a vacuous
uncertainty set from making the equivalence false. -/
theorem robust_terminal_iff (K : ι → Vec3 →ₗ[ℝ] V) (u : ι → ℝ)
    (n : ι → Vec3) (Q : ι → Set Vec3) (initial : V) (safe : V → Prop)
    (hn : ∀ j, n j ∈ Q j)
    (hnull : ∀ j q, q ∈ Q j → K j (q-n j) = 0) :
    (∀ q : ι → Vec3, (∀ j, q j ∈ Q j) → safe (initial+∑ j, u j • K j (q j))) ↔
      safe (initial+∑ j, u j • K j (n j)) := by
  constructor
  · intro h
    exact h n hn
  · intro h q hq
    rw [terminal_eq_nominal K u q n (fun j => hnull j (q j) (hq j))]
    exact h
end Terminal

/-- A zero first-order axial sensitivity does not mean exact decoupling:
the finite axial loss is precisely half the squared chord distance. -/
theorem axial_chord_loss (n q : Vec3) (hn : n ⬝ᵥ n = 1) (hq : q ⬝ᵥ q = 1) :
    n ⬝ᵥ (q-n) = -(enorm (q-n)^2)/2 := by
  have he := ThrustSupport.chord_sq n q hn hq
  rw [dotProduct_sub, hn]
  linarith

theorem axial_loss_strict (n q : Vec3) (hn : n ⬝ᵥ n = 1) (hq : q ⬝ᵥ q = 1)
    (hne : q ≠ n) : n ⬝ᵥ (q-n) < 0 := by
  rw [axial_chord_loss n q hn hq]
  have he : enorm (q-n) ≠ 0 := fun h => hne (sub_eq_zero.mp ((enorm_eq_zero_iff _).mp h))
  have hp := sq_pos_of_ne_zero he
  linarith

end GNC.DecoupledPlanning
