import GNC.Dynamics.GravityRemainderMonotone
import GNC.Dynamics.PolynomialOrbitCertificate

/-! A retained-direction predictor is a certified prediction only after its
complete physical defect is bounded. These results separate the computed
reference defect, the computed linear-response defect, and the exact
inverse-square gravity remainder, then close the physical error region.
The bounds concern prediction error, not displacement from the reference.
-/
noncomputable section
namespace GNC.Gravity
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The identity holds for computed references and responses: neither is
assumed to solve its defining differential equation exactly. -/
theorem retained_response_defect_identity (μ scale : ℝ) (q d qa da u du : E) :
    scale • (field μ (q+d)+(u+du))-(qa+da) =
      (scale • (field μ q+u)-qa) +
      (scale • (gradient μ q d+du)-da) +
      scale • (field μ (q+d)-field μ q-gradient μ q d) := by
  module

variable [CompleteSpace E]

/-- A fully computable bound: D bounds the retained response, not the
unknown physical error. No small-angle truncation is used. -/
theorem retained_response_defect_bound (μ scale : ℝ) (hμ : 0≤μ) (hscale : 0≤scale)
    (q d qa da u du : E) {D ε₀ ε₁ : ℝ}
    (hd : ‖d‖≤D) (hD : D<‖q‖)
    (h₀ : ‖scale • (field μ q+u)-qa‖≤ε₀)
    (h₁ : ‖scale • (gradient μ q d+du)-da‖≤ε₁) :
    ‖scale • (field μ (q+d)+(u+du))-(qa+da)‖ ≤
      ε₀+ε₁+scale*remainderBound μ ‖q‖ D := by
  rw [retained_response_defect_identity]
  have hrem := remainder_bound_of_norm_le μ hμ q d hd hD
  have hscaled : ‖scale • (field μ (q+d)-field μ q-gradient μ q d)‖ ≤
      scale*remainderBound μ ‖q‖ D := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscale]
    exact mul_le_mul_of_nonneg_left hrem hscale
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add h₀ h₁)) hscaled)

/-- All-time error bound against the full nonlinear orbit, using only
candidate-side radius and defect checks. Quantifying over the pointing
parameter outside this theorem gives a uniform family certificate. -/
theorem retained_response_prediction (μ scale : ℝ) (hμ : 0≤μ) (hscale : 0≤scale)
    (x xv q qv qa d dv da u du : ℝ → E) (D ε₀ ε₁ : ℝ → ℝ)
    {κ F r M : ℝ} (hκ : 0≤κ) (hk : κ<56) (hF : 0≤F) (hr : 0<r)
    (hclose : F*PolynomialSupersolution.value κ 1<M)
    (hlip : scale*(2*μ/r^3)≤κ)
    (hregion : ∀ t ∈ Icc (0:ℝ) 1, r+M≤‖q t+d t‖)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, ‖d t‖≤D t ∧ D t<‖q t‖)
    (h₀ : ∀ t ∈ Icc (0:ℝ) 1, ‖scale • (field μ (q t)+u t)-qa t‖≤ε₀ t)
    (h₁ : ∀ t ∈ Icc (0:ℝ) 1,
      ‖scale • (gradient μ (q t) (d t)+du t)-da t‖≤ε₁ t)
    (hbudget : ∀ t ∈ Icc (0:ℝ) 1,
      ε₀ t+ε₁ t+scale*remainderBound μ ‖q t‖ (D t)≤F)
    (hx : Continuous x) (hv : Continuous xv)
    (hq : Continuous q) (hqv : Continuous qv) (hc : Continuous d) (hcv : Continuous dv)
    (hdx : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt x (xv t) t)
    (hdv : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt xv (scale • (field μ (x t)+(u t+du t))) t)
    (hdq : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt q (qv t) t)
    (hdqv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt qv (qa t) t)
    (hdd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt d (dv t) t)
    (hddv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt dv (da t) t)
    (hip : x 0=q 0+d 0) (hiv : xv 0=qv 0+dv 0) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖x t-(q t+d t)‖≤F*PolynomialSupersolution.value κ 1 ∧
      ‖xv t-(qv t+dv t)‖≤F*PolynomialSupersolution.velocity κ 1 := by
  apply constant_prediction μ scale hμ hscale x xv
    (fun t => q t+d t) (fun t => qv t+dv t) (fun t => qa t+da t)
    (fun t => u t+du t) hκ hk hF hr hclose hlip hregion hx hv
    (hq.add hc) (hqv.add hcv) hdx hdv
    (fun t ht => (hdq t ht).add (hdd t ht))
    (fun t ht => (hdqv t ht).add (hddv t ht)) hip hiv
  intro t ht
  exact (retained_response_defect_bound μ scale hμ hscale
    (q t) (d t) (qa t) (da t) (u t) (du t)
    (hd t ht).1 (hd t ht).2 (h₀ t ht) (h₁ t ht)).trans (hbudget t ht)

end GNC.Gravity
