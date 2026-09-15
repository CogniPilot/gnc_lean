import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! Terminal rendezvous certificates apply to a command at a specified epoch.
Position and inertial relative velocity have separate budgets. These theorems
compose error certificates; they do not assume a solver tolerance bounds an
ODE error or establish the input certificates themselves.
-/
noncomputable section
namespace GNC.RendezvousError
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A validated physical endpoint encloses the error of any computed
prediction, regardless of which method produced it. Both directions matter:
comparing upper bounds alone does not compare actual errors. -/
theorem method_error (actual center prediction : E) {ε : ℝ}
    (h : ‖actual-center‖ ≤ ε) :
    ‖center-prediction‖-ε ≤ ‖actual-prediction‖ ∧
      ‖actual-prediction‖ ≤ ‖center-prediction‖+ε := by
  have hi := norm_sub_norm_le (actual-prediction) (center-prediction)
  have hj := norm_sub_norm_le (center-prediction) (actual-prediction)
  rw [sub_sub_sub_cancel_right] at hi hj
  rw [norm_sub_rev center actual] at hj
  constructor <;> linarith

/-- Dynamics truncation, evaluation, targeting residual and target ephemeris
uncertainty are charged separately, at the same terminal time. Apply this to
position and velocity separately, with their own units and limits. -/
theorem budget (actual ideal computed targetEstimate target : E)
    {model numerical targeting ephemeris : ℝ}
    (hm : ‖actual-ideal‖ ≤ model) (hn : ‖ideal-computed‖ ≤ numerical)
    (ht : ‖computed-targetEstimate‖ ≤ targeting)
    (he : ‖targetEstimate-target‖ ≤ ephemeris) :
    ‖actual-target‖ ≤ model+numerical+targeting+ephemeris := by
  have h1 := dist_triangle actual ideal computed
  have h2 := dist_triangle actual computed targetEstimate
  have h3 := dist_triangle actual targetEstimate target
  simp only [dist_eq_norm] at h1 h2 h3
  linarith

/-- A rotating coordinate derivative must include the frame-rate term before
it can be certified as an inertial relative velocity. -/
theorem inertial_velocity_budget (Ω : E →L[ℝ] E) (p v : E) {ep ev : ℝ}
    (hp : ‖p‖ ≤ ep) (hv : ‖v‖ ≤ ev) :
    ‖v+Ω p‖ ≤ ev+‖Ω‖*ep := by
  exact (norm_add_le _ _).trans (add_le_add hv
    ((Ω.le_opNorm p).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))))

/-- A planner need only supply a feasible command. Its internal optimization
algorithm need not be trusted when its terminal residual and all error terms
are independently checked. No optimality claim follows from this theorem. -/
theorem certified_command {U : Type*} (u : U)
    (actual ideal computed targetEstimate target : U → E)
    {model numerical targeting ephemeris limit : ℝ}
    (hm : ‖actual u-ideal u‖ ≤ model) (hn : ‖ideal u-computed u‖ ≤ numerical)
    (ht : ‖computed u-targetEstimate u‖ ≤ targeting)
    (he : ‖targetEstimate u-target u‖ ≤ ephemeris)
    (hlimit : model+numerical+targeting+ephemeris ≤ limit) :
    ‖actual u-target u‖ ≤ limit :=
  (budget _ _ _ _ _ hm hn ht he).trans hlimit

end GNC.RendezvousError
