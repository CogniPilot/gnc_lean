import GNC.Dynamics.LogDynamics
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Exact state-dependent exponential-coordinate dynamics.

These identities allow an arbitrary state-dependent coefficient. The SE2(3)
result uses the previously verified finite exponential differential and its
inverse, including zero rotation. It is an exact ODE equivalence on an
exponential chart, not a quadrature formula, convergence assertion for a
Magnus series, or solution in closed form.
-/
noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.Operator
namespace GNC.StateDependentMagnus

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The state derivative adds two terms to a pointwise matrix commutator.
The opposite of mathlib's vector-field bracket matches [A,B]=AB-BA for
linear vector fields. A and B can be time slices of A(t,x). -/
theorem coefficient_bracket {A B : E → E →L[ℝ] E}
    {DA DB : E →L[ℝ] E →L[ℝ] E} (x : E)
    (hA : HasFDerivAt A DA x) (hB : HasFDerivAt B DB x) :
    VectorField.lieBracket ℝ (fun y => B y y) (fun y => A y y) x =
      A x (B x x)-B x (A x x)+DA (B x x) x-DB (A x x) x := by
  have ha := hA.clm_apply (hasFDerivAt_id x)
  have hb := hB.clm_apply (hasFDerivAt_id x)
  simp only [id_eq] at ha hb
  simp only [VectorField.lieBracket, ha.fderiv, hb.fderiv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply]
  abel

end General

/-- Prescribed inputs and state dependence both remain inside the exact
log-coordinate equation; there is no reference-gravity substitution. -/
def logRate (ξ : ℝ → SE23 → LogState) (t : ℝ) (x : LogState) : LogState :=
  Jacobian.blockInverse x (ξ t (groupExp x))

theorem reconstruction {ξ : ℝ → SE23 → LogState} {x : ℝ → LogState} {t : ℝ}
    (hx : HasDerivAt x (logRate ξ t (x t)) t)
    (hchart : enorm (x t 2) < 2*Real.pi) :
    HasDerivAt (fun s => NormedSpace.exp (hat (x s)))
      (hat (ξ t (groupExp (x t)))*NormedSpace.exp (hat (x t))) t := by
  simpa only [logRate, Jacobian.blockLeft_inverse_all _ _ hchart] using
    matrixExp_curve_derivative_all hx

/-- Converse for a differentiable logarithm: the physical matrix equation
forces the exact coordinate rate. No independent tangent-rate assumption
is used. -/
theorem coordinate_rate {ξ : ℝ → SE23 → LogState} {x : ℝ → LogState}
    {y : LogState} {t : ℝ} (hx : HasDerivAt x y t)
    (hchart : enorm (x t 2) < 2*Real.pi)
    (hphysical : HasDerivAt (fun s => NormedSpace.exp (hat (x s)))
      (hat (ξ t (groupExp (x t)))*NormedSpace.exp (hat (x t))) t) :
    y = logRate ξ t (x t) :=
  log_curve_derivative hx hchart hphysical

end GNC.StateDependentMagnus
