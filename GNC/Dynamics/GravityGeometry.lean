import GNC.Dynamics.GravityField

/-! Exact geometric structure of state-dependent central gravity.
Rotation covariance and inverse-square homogeneity reduce gravity deviations
to a universal dimensionless nonlinear map. The secant identity is exact;
it does not replace the field by its derivative at the reference trajectory. -/
noncomputable section
open Set Real MeasureTheory
namespace GNC.Gravity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem field_isometry (μ : ℝ) (Q : E ≃ₗᵢ[ℝ] E) (q : E) :
    field μ (Q q) = Q (field μ q) := by
  simp [field, Q.norm_map, map_smul]

theorem field_parameter (μ : ℝ) (q : E) : field μ q = μ • field 1 q := by
  simp only [field, smul_smul]
  congr 1
  ring

theorem field_positive_scale (μ c : ℝ) (hc : 0 < c) (q : E) :
    field μ (c • q) = (1/c^2) • field μ q := by
  by_cases hq : q = 0
  · simp [hq, field]
  · have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have hc0 := hc.ne'
    simp only [field, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
    congr 1
    field_simp

/-- No local linearization: all orientation and length-scale dependence
is separated exactly. The remaining function is the unit-parameter field. -/
theorem normalized_difference (μ c : ℝ) (hc : 0 < c)
    (Q : E ≃ₗᵢ[ℝ] E) (q δ : E) :
    field μ (c • Q (q+δ))-field μ (c • Q q) =
      (μ/c^2) • Q (field 1 (q+δ)-field 1 q) := by
  rw [field_positive_scale μ c hc, field_positive_scale μ c hc,
    field_isometry, field_isometry, field_parameter μ (q+δ), field_parameter μ q]
  simp only [map_smul, map_sub, smul_sub, smul_smul]
  module

/-- Full nonlinear gravity residual at unit reference radius. For a unit
q, the only nonlinear scalar is the inverse cube of the displaced radius. -/
theorem unit_reference_difference (q δ : E) (hq : ‖q‖ = 1) :
    field 1 (q+δ)-field 1 q = q-(1/‖q+δ‖^3) • (q+δ) := by
  simp only [field, hq, one_pow, div_one, neg_smul, one_smul]
  module

theorem displaced_radius_squared (q δ : E) (hq : ‖q‖ = 1) :
    ‖q+δ‖^2 = 1+2*inner ℝ q δ+‖δ‖^2 := by
  rw [norm_add_sq_real, hq]
  ring

theorem exact_radial_coefficients (μ : ℝ) (q δ : E) :
    field μ (q+δ)-field μ q =
      (-μ/‖q+δ‖^3) • δ+(μ/‖q‖^3-μ/‖q+δ‖^3) • q := by
  simp only [field, smul_add, sub_smul, neg_div, neg_smul]
  module

variable [CompleteSpace E]

/-- An exact state-dependent secant representation. Its integral depends
on the displacement, so it is not a known time-only linear generator. -/
theorem secant_integral (μ : ℝ) (q δ : E) (hd : ‖δ‖ < ‖q‖) :
    field μ (q+δ)-field μ q =
      ∫ s in (0:ℝ)..1, gradient μ (q+s • δ) δ := by
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun r : ℝ => field μ (q+r • δ)) (gradient μ (q+s • δ) δ) s := by
    apply field_derivative μ
      (by simpa using ((hasDerivAt_id s).smul_const δ).const_add q)
      (segment_nonzero q δ hd s hs)
  have hc : ContinuousOn (fun s : ℝ => gradient μ (q+s • δ) δ) (Icc 0 1) := by
    intro s hs
    have hn : 0 < ‖q+s • δ‖ := norm_pos_iff.mpr (segment_nonzero q δ hd s hs)
    apply ContinuousAt.continuousWithinAt
    unfold gradient
    fun_prop (disch := positivity)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hder s (by simpa using hs)) (hc.intervalIntegrable_of_Icc (by norm_num))
  simpa using he.symm

end GNC.Gravity

namespace GNC.Gravity
/-- Positive-radius points already obstruct affine translation dynamics;
the example does not use or cross the collision singularity. -/
theorem radial_second_difference (μ : ℝ) :
    field μ (3 : ℝ)-2*field μ (2 : ℝ)+field μ (1 : ℝ) = -(11/18)*μ := by
  norm_num [field, Real.norm_eq_abs]
  ring

theorem radial_not_affine (μ : ℝ) (hμ : 0 < μ) :
    field μ (3 : ℝ)-field μ (1 : ℝ) ≠
      2*(field μ (2 : ℝ)-field μ (1 : ℝ)) := by
  have he := radial_second_difference μ
  intro h
  linarith
end GNC.Gravity
