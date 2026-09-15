import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Tactic

/-! Exact nonlinear interaction coordinates. K can be a known drift flow,
including a nonlinear Kepler or Stark flow. The derivative hypotheses must
be proved for the chosen K; this generic chain-rule theorem does not itself
construct either orbital flow. State dependence is retained throughout.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.NonlinearInteraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The total differential of a time-dependent drift flow with spatial
derivative D and time derivative v. -/
def flowDifferential (v : E) (D : E →L[ℝ] E) : (ℝ × E) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ E).smulRight v +
    D.comp (ContinuousLinearMap.snd ℝ ℝ E)

/-- Pulling the perturbation back by the full nonlinear flow derivative
exactly removes the drift. No linearization at a reference is taken. -/
theorem reconstruction {K : (ℝ × E) → E} {z : ℝ → E} {t : ℝ}
    (drift perturbation : E → E) (D : E ≃L[ℝ] E)
    (hK : HasFDerivAt K (flowDifferential (drift (K (t,z t)))
      (D : E →L[ℝ] E)) (t,z t))
    (hz : HasDerivAt z (D.symm (perturbation (K (t,z t)))) t) :
    HasDerivAt (fun s => K (s,z s))
      (drift (K (t,z t))+perturbation (K (t,z t))) t := by
  have h := hK.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hz)
  simpa [flowDifferential] using h

/-- Conversely, a differentiable interaction-coordinate path that
reconstructs the physical solution must satisfy the pulled-back equation. -/
theorem coordinate_rate {K : (ℝ × E) → E} {z : ℝ → E} {t : ℝ} {v : E}
    (drift perturbation : E → E) (D : E ≃L[ℝ] E)
    (hK : HasFDerivAt K (flowDifferential (drift (K (t,z t)))
      (D : E →L[ℝ] E)) (t,z t))
    (hz : HasDerivAt z v t)
    (hphysical : HasDerivAt (fun s => K (s,z s))
      (drift (K (t,z t))+perturbation (K (t,z t))) t) :
    v = D.symm (perturbation (K (t,z t))) := by
  have h := (hK.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hz)).unique hphysical
  have he : D v = perturbation (K (t,z t)) := by
    simpa [flowDifferential] using h
  exact D.injective (by simpa using he)

end GNC.NonlinearInteraction
