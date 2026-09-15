import GNC.Dynamics.GravityField

/-! The speed-dependent drag map w ↦ ‖w‖w. Its first-order remainder has
a global quadratic bound, obtained directly from norm geometry. No local
Hessian enclosure or sampled Jacobian is assumed. -/
noncomputable section
open Real
open scoped RealInnerProductSpace
namespace GNC.QuadraticDrag
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def field (w : E) : E := ‖w‖ • w
def linear (w h : E) : E := ‖w‖ • h+(⟪w,h⟫/‖w‖) • w

theorem field_derivative {w : ℝ → E} {h : E} {t : ℝ}
    (hw : HasDerivAt w h t) (hz : w t ≠ 0) :
    HasDerivAt (fun s => field (w s)) (linear (w t) h) t := by
  convert (Gravity.norm_derivative hw hz).smul hw using 1

theorem norm_change (w h : E) : |‖w+h‖-‖w‖| ≤ ‖h‖ := by
  simpa using abs_norm_sub_norm_le (w+h) w

/-- An exact identity behind both the density and drag remainders. -/
theorem norm_linear_identity (w h : E) (hw : w ≠ 0) :
    2*‖w‖*(‖w+h‖-‖w‖-⟪w,h⟫/‖w‖) = ‖h‖^2-(‖w+h‖-‖w‖)^2 := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hs := norm_add_sq_real w h
  field_simp
  nlinarith [congrArg (fun x : ℝ => ‖w‖*x) hs]

theorem norm_linear_remainder (w h : E) (hw : w ≠ 0) :
    0 ≤ ‖w+h‖-‖w‖-⟪w,h⟫/‖w‖ ∧
      ‖w+h‖-‖w‖-⟪w,h⟫/‖w‖ ≤ ‖h‖^2/(2*‖w‖) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hi := norm_linear_identity w h hw
  have hd := norm_change w h
  have hs : (‖w+h‖-‖w‖)^2 ≤ ‖h‖^2 := by
    nlinarith [sq_abs (‖w+h‖-‖w‖),
      mul_self_le_mul_self (abs_nonneg (‖w+h‖-‖w‖)) hd]
  constructor
  · nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2*‖w‖)).mpr
    nlinarith [sq_nonneg (‖w+h‖-‖w‖)]

theorem field_norm (w : E) : ‖field w‖ = ‖w‖^2 := by
  simp [field, norm_smul, pow_two]

/-- The drag map is differentiable even at zero relative wind, where the
norm alone is not differentiable. Its derivative there is zero. -/
theorem field_fderiv_zero : HasFDerivAt (field (E := E)) (0 : E →L[ℝ] E) 0 := by
  rw [hasFDerivAt_iff_tendsto]
  have he (w : E) : ‖w‖⁻¹*‖w‖^2 = ‖w‖ := by
    by_cases hw : w = 0
    · simp [hw]
    · field_simp [norm_ne_zero_iff.mpr hw]
  simpa only [sub_zero, ContinuousLinearMap.zero_apply, field, norm_zero,
    zero_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    ← pow_two, he] using (continuous_norm.tendsto (0 : E))

theorem field_derivative_all {w : ℝ → E} {h : E} {t : ℝ}
    (hw : HasDerivAt w h t) :
    HasDerivAt (fun s => field (w s)) (linear (w t) h) t := by
  by_cases hz : w t = 0
  · have hf : HasFDerivAt (field (E := E)) (0 : E →L[ℝ] E) (w t) := by
      rw [hz]
      exact field_fderiv_zero
    simpa [hz, linear] using hf.comp_hasDerivAt t hw
  · exact field_derivative hw hz

theorem linear_bound (w h : E) : ‖linear w h‖ ≤ 2*‖w‖*‖h‖ := by
  by_cases hw : w = 0
  · simp [hw, linear]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hi := abs_real_inner_le_norm w h
  have hq : |⟪w,h⟫/‖w‖| * ‖w‖ ≤ ‖w‖*‖h‖ := by
    rw [abs_div, abs_of_pos hn, div_mul_cancel₀ _ (ne_of_gt hn)]
    exact hi
  have ht := norm_add_le (‖w‖ • h) ((⟪w,h⟫/‖w‖) • w)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)] at ht
  dsimp [linear]
  linarith

/-- A global bound, including w=0. The coefficient is exactly one. -/
theorem remainder_bound (w h : E) : ‖field (w+h)-field w-linear w h‖ ≤ ‖h‖^2 := by
  by_cases hw : w = 0
  · simpa [hw, linear, field] using (field_norm h).le
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let d := ‖w+h‖-‖w‖
  let e := d-⟪w,h⟫/‖w‖
  have he : 0 ≤ e := (norm_linear_remainder w h hw).1
  have hi : 2*‖w‖*e = ‖h‖^2-d^2 := norm_linear_identity w h hw
  have hid : field (w+h)-field w-linear w h = d • h+e • w := by
    dsimp [field, linear, d, e]
    module
  rw [hid]
  have ht := norm_add_le (d • h) (e • w)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg he] at ht
  have hd := norm_change w h
  change |d| ≤ ‖h‖ at hd
  nlinarith [sq_nonneg (‖h‖-|d|), sq_abs d]

end GNC.QuadraticDrag
