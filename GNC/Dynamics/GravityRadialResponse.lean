import GNC.Dynamics.GravityHessianBilinear

/-! Radial/transverse components of the derivatives of inverse-square gravity.
These specialize the derivatives of the physical field, rather than declaring
a quadratic surrogate. The transverse quadratic term has a positive sign.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gradient_radial_transverse (μ r x : ℝ) (k w : E)
    (hr : 0 < r) (hk : ‖k‖ = 1) (hw : ⟪k,w⟫ = 0) :
    gradient μ (r • k) (x • k+w) = (μ/r^3) • ((2*x) • k-w) := by
  have hn : ‖r • k‖ = r := by simp [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hk]
  have hi : ⟪k,k⟫ = 1 := by rw [real_inner_self_eq_norm_sq,hk]; norm_num
  unfold gradient
  simp only [hn,inner_add_right,real_inner_smul_left,real_inner_smul_right,hi,hw]
  match_scalars <;> field_simp <;> ring

/-- At radius `r`, the radial coefficient is
`μ/r⁴ * (-3 x² + 3/2 ‖w‖²)` and the transverse vector is
`μ/r⁴ * (3 x) • w`, where `w` is perpendicular to the radial unit vector. -/
theorem half_hessian_radial_transverse (μ r x : ℝ) (k w : E)
    (hr : 0 < r) (hk : ‖k‖ = 1) (hw : ⟪k,w⟫ = 0) :
    (1/2:ℝ) • hessian μ (r • k) (x • k+w) (x • k+w) =
      (μ/r^4) • ((-3*x^2+(3/2:ℝ)*‖w‖^2) • k+(3*x) • w) := by
  have hn : ‖r • k‖ = r := by simp [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hk]
  have hi : ⟪k,k⟫ = 1 := by rw [real_inner_self_eq_norm_sq,hk]; norm_num
  have hw' : ⟪w,k⟫ = 0 := by rw [real_inner_comm,hw]
  unfold hessian
  simp only [hn,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,hi,hw,hw',real_inner_self_eq_norm_sq,
    norm_smul,Real.norm_eq_abs,hk,mul_one,sq_abs]
  match_scalars <;> field_simp <;> ring

end GNC.Gravity
