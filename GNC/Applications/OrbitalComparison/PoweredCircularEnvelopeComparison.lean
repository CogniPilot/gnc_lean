import GNC.Dynamics.GeometricEnvelopeComparison
import GNC.Applications.OrbitalComparison.PoweredCircularComparators

/-! The sixfold advantage of the ideal geometric envelope holds at every
positive time, not just at the endpoint. It is a ratio of sufficient error
bounds, not a lower bound on the Cartesian predictor's actual error. -/
noncomputable section
namespace GNC.OrbitalComparison.PoweredCircularEnvelopeComparison
open Set PoweredCircularLogTube PoweredCircularComparators

/-- The new general definitions reproduce the physically certified budgets. -/
theorem envelopes_agree (t : ℝ) :
    GeometricEnvelopeComparison.geometric F₂ (gravityDefect/3) κ t=errorBudget t ∧
    GeometricEnvelopeComparison.cartesian angleDefect (gravityDefect/3) κ t=
      budget angleDefect t := by
  constructor <;>
    simp only [GeometricEnvelopeComparison.geometric, GeometricEnvelopeComparison.cartesian,
      errorBudget, budget, F₄, gravityDefect] <;> ring

/-- This verifies the input-dependent criterion, without sampling times. -/
theorem ratio_criterion : F₂/6+(4-3*(1/6:ℝ))*(gravityDefect/3)/15 < angleDefect/6 := by
  norm_num [F₂, gravityDefect, angleDefect, L, μ, U, angleRadius, earthMu,
    duration, lengthScale, physicalAcceleration, PolynomialSupersolution.value,
    PolynomialSupersolution.polynomial]

theorem sixfold_on {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    6*errorBudget t<budget angleDefect t := by
  have hμ := μ_nonneg
  have hL := checks.1
  have hθ : 0≤angleRadius := by norm_num [angleRadius]
  have hK : 0≤F₂ := by unfold F₂; positivity
  have hH : 0≤gravityDefect/3 := by unfold gravityDefect; positivity
  have hc := GeometricEnvelopeComparison.uniform_ratio (F := angleDefect) hK hH checks.2.2.1
    checks.2.2.2.1 (q := (1/6:ℝ)) (by norm_num) (by norm_num)
    (by nlinarith [ratio_criterion]) t ht
  rw [(envelopes_agree t).1, (envelopes_agree t).2] at hc
  linarith

end GNC.OrbitalComparison.PoweredCircularEnvelopeComparison
