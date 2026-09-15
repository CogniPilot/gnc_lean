import GNC.Dynamics.GravityRemainderBall

/-! A time-dependent reference expansion retains spatial gravity error.
These pointwise identities apply at every time, also when the reference and
its gradient have been computed approximately. The complete physical defect
includes reference, response, gradient and nonlinear-gravity contributions.
No Magnus convergence or numerical evaluation accuracy is assumed here.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Physical acceleration minus the supplied candidate acceleration. -/
def accelerationDefect (μ : ℝ) (q u qdd : E) : E := field μ q+u-qdd

omit [CompleteSpace E] in
/-- Exact decomposition of a predicted position `q+d`. Here `L` is the
retained time-dependent gradient at the current time, `u+du` is physical
thrust acceleration, and `qdd+ddd` is the candidate second derivative. -/
theorem reference_prediction_defect_split (μ : ℝ) (q d u du qdd ddd : E)
    (L : E →L[ℝ] E) :
    accelerationDefect μ (q+d) (u+du) (qdd+ddd) =
      accelerationDefect μ q u qdd+(L d+du-ddd)+
      (gradient μ q d-L d)+(field μ (q+d)-field μ q-gradient μ q d) := by
  unfold accelerationDefect
  abel

/-- An approximation of the known reference gradient incurs a linear-in-
displacement error in addition to the true spatial Taylor remainder. -/
theorem approximate_gradient_remainder (μ : ℝ) (hμ : 0 ≤ μ) (q d : E)
    (L : E →L[ℝ] E) {eps : ℝ} (hd : ‖d‖ < ‖q‖)
    (hL : ‖gradient μ q d-L d‖ ≤ eps*‖d‖) :
    ‖field μ (q+d)-field μ q-L d‖ ≤
      eps*‖d‖+remainderBound μ ‖q‖ ‖d‖ := by
  have he : field μ (q+d)-field μ q-L d =
      (gradient μ q d-L d)+(field μ (q+d)-field μ q-gradient μ q d) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hL (remainder_bound μ hμ q d hd))

/-- A computable residual budget for the full inverse-square prediction.
`referenceError` charges a reference that is not an exact physical solution;
`responseError` charges time integration (Magnus or otherwise) and forcing
evaluation; `gradientError` charges approximation of the reference gradient.
The last, sharp term persists even when the first three errors are zero.
All quantities may be time dependent; the theorem is applied pointwise. -/
theorem reference_prediction_defect_bound (μ : ℝ) (hμ : 0 ≤ μ)
    (q d u du qdd ddd : E) (L : E →L[ℝ] E)
    {referenceError responseError gradientError : ℝ} (hd : ‖d‖ < ‖q‖)
    (href : ‖accelerationDefect μ q u qdd‖ ≤ referenceError)
    (hresponse : ‖L d+du-ddd‖ ≤ responseError)
    (hgradient : ‖gradient μ q d-L d‖ ≤ gradientError*‖d‖) :
    ‖accelerationDefect μ (q+d) (u+du) (qdd+ddd)‖ ≤
      referenceError+responseError+gradientError*‖d‖+
        remainderBound μ ‖q‖ ‖d‖ := by
  rw [reference_prediction_defect_split μ q d u du qdd ddd L]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add href hresponse)) hgradient))
    (remainder_bound μ hμ q d hd))

/-- A regional version retains the actual displacement squared. The radius
gap is a validity hypothesis, not a numerical tolerance or inferred tube. -/
theorem reference_prediction_defect_quadratic (μ : ℝ) (hμ : 0 ≤ μ)
    (q d u du qdd ddd : E) (L : E →L[ℝ] E)
    {r D referenceError responseError gradientError : ℝ}
    (hD : D < r) (hq : r ≤ ‖q‖) (hd : ‖d‖ ≤ D)
    (href : ‖accelerationDefect μ q u qdd‖ ≤ referenceError)
    (hresponse : ‖L d+du-ddd‖ ≤ responseError)
    (hgradient : ‖gradient μ q d-L d‖ ≤ gradientError*‖d‖) :
    ‖accelerationDefect μ (q+d) (u+du) (qdd+ddd)‖ ≤
      referenceError+responseError+gradientError*‖d‖+
        (3*μ/(r-D)^4)*‖d‖^2 := by
  rw [reference_prediction_defect_split μ q d u du qdd ddd L]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add href hresponse)) hgradient))
    (remainder_quadratic μ hμ q d hD hq hd))

omit [CompleteSpace E] in
/-- Actual velocity error about an arbitrary differentiable reference.
The reference acceleration defect vanishes only for a physical reference
with the stated reference thrust. No linearized ODE is assumed. -/
theorem relative_velocity_derivative (μ : ℝ)
    {v vref : ℝ → E} {p q u uref qdd : E} {t : ℝ}
    (hv : HasDerivAt v (field μ p+u) t) (hq : HasDerivAt vref qdd t) :
    HasDerivAt (fun s => v s-vref s)
      (gradient μ q (p-q)+(u-uref)+
        (field μ p-field μ q-gradient μ q (p-q))+
        accelerationDefect μ q uref qdd) t := by
  convert hv.sub hq using 1
  unfold accelerationDefect
  abel

/-- The sharp inward-radial nonlinear acceleration defect is strictly
positive. Exact propagation of a reference gradient cannot remove it. -/
theorem radial_nonlinear_defect_pos (μ r d : ℝ) (hμ : 0 < μ)
    (hd : 0 < d) (hdr : d < r) :
    0 < μ/(r-d)^2-μ/r^2-2*μ*d/r^3 := by
  have hr : 0 < r := hd.trans hdr
  rw [radial_remainder_exact μ r d hr.ne' (sub_pos.mpr hdr).ne']
  unfold remainderBound
  have hnum : 0 < 3*r-2*d := by linarith
  have hgap : 0 < r-d := sub_pos.mpr hdr
  positivity

end GNC.Gravity
