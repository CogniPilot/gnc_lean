import GNC.Dynamics.InverseRadius

/-! Exact vector identity underlying the full-field inverse-radius certificate. -/
noncomputable section
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The field norm error is exactly a scalar multiple of the algebraic
constraint residual when the proposed inverse radius is nonnegative. -/
theorem field_inverse_radius_identity (μ : ℝ) (hμ : 0 ≤ μ) (q : E) {u : ℝ}
    (hq : 0 < ‖q‖) (hu : 0 ≤ u) :
    ‖field μ q-(-μ*u^3) • q‖ =
      μ/‖q‖^2*inverseRadiusFactor (‖q‖*u)*|‖q‖^2*u^2-1| := by
  have he : field μ q-(-μ*u^3) • q = (μ*(u^3-1/‖q‖^3)) • q := by
    unfold field
    rw [← sub_smul]
    congr 1
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hμ,mul_assoc,
    inverse_cube_defect hq hu]
  ring

end GNC.Gravity
