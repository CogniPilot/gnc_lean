import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

/-! Coordinate-free tube bookkeeping for feedback motion planning/MPC.

This proves constraint tightening, propagation and reference reset for a
specified controller/step map. It does not establish optimality, recursive
feasibility, a terminal set or a continuous intersample certificate for MPC.
Those require additional control/model-specific results.
-/
namespace GNC.GroupTube
variable {G W U : Type*} [Group G]

/-- Right multiplicative error: actual = reference * error. -/
def tube (reference : G) (errors : Set G) : Set G :=
  {x | reference⁻¹*x ∈ errors}

def tightened (safe errors : Set G) : Set G :=
  {reference | ∀ e ∈ errors, reference*e ∈ safe}

theorem tightened_sound {safe errors : Set G} {reference x : G}
    (hr : reference ∈ tightened safe errors) (hx : x ∈ tube reference errors) :
    x ∈ safe := by
  simpa only [mul_inv_cancel_left] using hr (reference⁻¹*x) hx

/-- An exact error-set reset when the planner changes reference. Reusing
the old error set unchanged is generally unsound. This identity is global
on a group; converting its image back to log coordinates needs a chart. -/
theorem reference_reset {oldReference newReference x : G} {errors : Set G}
    (hx : x ∈ tube oldReference errors) :
    x ∈ tube newReference ((fun e => newReference⁻¹*oldReference*e) '' errors) := by
  refine ⟨oldReference⁻¹*x,hx,?_⟩
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Universal propagation through a specified disturbed step map.
The error enclosure is a premise to discharge using a validated flow
certificate, not an enclosure inferred from simulated trajectories. -/
theorem trajectory_enclosure (step : ℕ → G → W → G)
    (reference x : ℕ → G) (errors : ℕ → Set G)
    (disturbances : ℕ → Set W) (w : ℕ → W)
    (hstep : ∀ k, x (k+1)=step k (x k) (w k))
    (hw : ∀ k, w k ∈ disturbances k)
    (hinit : x 0 ∈ tube (reference 0) (errors 0))
    (hpropagate : ∀ k e, e ∈ errors k → ∀ d ∈ disturbances k,
      (reference (k+1))⁻¹*step k (reference k*e) d ∈ errors (k+1)) :
    ∀ k, x k ∈ tube (reference k) (errors k) := by
  intro k
  induction k with
  | zero => exact hinit
  | succ k ih =>
    have h := hpropagate k ((reference k)⁻¹*x k) ih (w k) (hw k)
    simpa only [mul_inv_cancel_left, ← hstep k] using h

/-- State and implemented-feedback input constraints follow from the same
joint error enclosure. The feedback may be PID, MPC or learned; its input
bound must hold throughout the set, including controller internal states. -/
theorem state_input_constraints (reference x : ℕ → G) (errors safe : ℕ → Set G)
    (feedback : ℕ → G → U) (inputs : ℕ → Set U)
    (htube : ∀ k, x k ∈ tube (reference k) (errors k))
    (htight : ∀ k, reference k ∈ tightened (safe k) (errors k))
    (hinput : ∀ k e, e ∈ errors k → feedback k (reference k*e) ∈ inputs k) :
    ∀ k, x k ∈ safe k ∧ feedback k (x k) ∈ inputs k := by
  intro k
  refine ⟨tightened_sound (htight k) (htube k),?_⟩
  simpa only [mul_inv_cancel_left] using hinput k ((reference k)⁻¹*x k) (htube k)

end GNC.GroupTube
