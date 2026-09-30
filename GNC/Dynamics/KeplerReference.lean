import GNC.Dynamics.GravityReferenceDefect

/-! Exact Kepler-reference deviation and its quadratic gravity defect.

These theorems start from the physical differential equations. They do not
assume a small-angle attitude approximation, or an exact floating-point
Kepler solver. Numerical reference/response defects are charged explicitly.
The quadratic improvement is shared by Cartesian Encke formulations; it is
not a theorem that Lie coordinates always cost less.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.KeplerReference
open Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Subtract an unforced Kepler velocity equation from the thrusting equation.
The gravity gradient is retained and the remaining gravity is exactly quadratic
and higher in physical displacement, with the bound proved below. -/
theorem deviation_equation (μ : ℝ) {v w : ℝ → E} {p q u : E} {t : ℝ}
    (hv : HasDerivAt v (field μ p+u) t)
    (hw : HasDerivAt w (field μ q) t) :
    HasDerivAt (fun s => v s-w s)
      (gradient μ q (p-q)+u+(field μ p-field μ q-gradient μ q (p-q))) t := by
  convert hv.sub hw using 1
  abel

omit [CompleteSpace E] in
/-- Exact cancellation of reference gravity and the retained variational
response. The full nonlinear field at the candidate remains in the defect. -/
theorem linear_response_defect (μ : ℝ) (q d u : E) :
    accelerationDefect μ (q+d) u (field μ q+(gradient μ q d+u)) =
      field μ (q+d)-field μ q-gradient μ q d := by
  unfold accelerationDefect
  abel

theorem linear_response_defect_bound (μ : ℝ) (hμ : 0 ≤ μ) (q d u : E)
    {r D : ℝ} (hD : D < r) (hq : r ≤ ‖q‖) (hd : ‖d‖ ≤ D) :
    ‖accelerationDefect μ (q+d) u (field μ q+(gradient μ q d+u))‖ ≤
      (3*μ/(r-D)^4)*‖d‖^2 := by
  rw [linear_response_defect]
  exact remainder_quadratic μ hμ q d hD hq hd

/-- A numerical Kepler reference and a numerical forced variational response
retain the same quadratic spatial remainder, plus their actual residuals.
All bounds are pointwise, to be checked throughout the step. -/
theorem approximate_response_defect_bound (μ : ℝ) (hμ : 0 ≤ μ)
    (q d u qdd ddd : E) {r D εK εd : ℝ}
    (hD : D < r) (hq : r ≤ ‖q‖) (hd : ‖d‖ ≤ D)
    (hK : ‖field μ q-qdd‖ ≤ εK)
    (hresponse : ‖gradient μ q d+u-ddd‖ ≤ εd) :
    ‖accelerationDefect μ (q+d) u (qdd+ddd)‖ ≤
      εK+εd+(3*μ/(r-D)^4)*‖d‖^2 := by
  have hid : accelerationDefect μ (q+d) u (qdd+ddd) =
      (field μ q-qdd)+(gradient μ q d+u-ddd)+
        (field μ (q+d)-field μ q-gradient μ q d) := by
    unfold accelerationDefect
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hK hresponse))
    (remainder_quadratic μ hμ q d hD hq hd))

end GNC.KeplerReference
