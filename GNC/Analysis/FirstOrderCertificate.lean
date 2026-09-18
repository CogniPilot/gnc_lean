import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! The first-order certificate: a scalar supersolution fences the norm of a
differentiable error. Three forms: the direct everywhere fencing, the
boundary-guarded form with strict margin, and the curvature specialization
`P' > κP + f`. -/
noncomputable section
namespace GNC.FirstOrderCertificate
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Everywhere defect bound: the direct fencing form. -/
theorem certificate (e de : ℝ → E) (P W : ℝ → ℝ) {T : ℝ}
    (he : Continuous e) (hde : ∀ t ∈ Ico 0 T, HasDerivAt e (de t) t)
    (hP : ∀ t, HasDerivAt P (W t) t) (hi : ‖e 0‖ ≤ P 0)
    (ha : ∀ t ∈ Ico 0 T, ‖de t‖ ≤ W t) :
    ∀ t ∈ Icc 0 T, ‖e t‖ ≤ P t :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary he.continuousOn
    (fun t ht => (hde t ht).hasDerivWithinAt) hi hP ha

/-- The defect bound is needed only at the boundary ‖e‖ = P, with strict
supersolution margin. -/
theorem certificate_boundary (e de : ℝ → E) (P W : ℝ → ℝ) {T : ℝ}
    (he : Continuous e) (hde : ∀ t ∈ Ico 0 T, HasDerivAt e (de t) t)
    (hP : ∀ t, HasDerivAt P (W t) t) (hi : ‖e 0‖ ≤ P 0)
    (ha : ∀ t ∈ Ico 0 T, ‖e t‖ = P t → ‖de t‖ < W t) :
    ∀ t ∈ Icc 0 T, ‖e t‖ ≤ P t := by
  have hPc : ContinuousOn P (Icc 0 T) :=
    fun t _ => (hP t).continuousAt.continuousWithinAt
  have hPd : ∀ t ∈ Ico (0:ℝ) T, HasDerivWithinAt P (W t) (Ici t) t :=
    fun t _ => (hP t).hasDerivWithinAt
  apply image_le_of_liminf_slope_right_lt_deriv_boundary'
    (continuous_norm.comp_continuousOn he.continuousOn)
    (fun x hx r hr => ((hde x hx).hasDerivWithinAt).liminf_right_slope_norm_le hr)
    hi hPc hPd
  exact fun x hx hbx => ha x hx hbx

/-- The curvature form: a defect bounded by `κ‖e‖ + f` is fenced by any
strict supersolution with `P' > κP + f`. -/
theorem certificate_curvature (e de : ℝ → E) (f P W : ℝ → ℝ) {T κ : ℝ}
    (he : Continuous e) (hde : ∀ t ∈ Ico 0 T, HasDerivAt e (de t) t)
    (hP : ∀ t, HasDerivAt P (W t) t) (hi : ‖e 0‖ ≤ P 0)
    (ha : ∀ t ∈ Ico 0 T, ‖de t‖ ≤ κ * ‖e t‖ + f t)
    (hW : ∀ t ∈ Ico 0 T, κ * P t + f t < W t) :
    ∀ t ∈ Icc 0 T, ‖e t‖ ≤ P t :=
  certificate_boundary e de P W he hde hP hi (fun t ht hbt =>
    lt_of_le_of_lt ((ha t ht).trans (by rw [hbt])) (hW t ht))

end GNC.FirstOrderCertificate
