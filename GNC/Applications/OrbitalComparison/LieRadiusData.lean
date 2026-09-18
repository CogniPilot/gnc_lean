import GNC.Applications.OrbitalComparison.LieRadiusData.Z
import GNC.Applications.OrbitalComparison.LieRadiusData.H
import GNC.Applications.OrbitalComparison.LieRadiusData.U
import GNC.Applications.OrbitalComparison.LieRadiusData.ConstraintLinear
import GNC.Applications.OrbitalComparison.LieRadiusData.LieResidual

/-! Uniform bounds from independently cached kernel-checked range records.
These are necessary stages of the direct certificate. The concrete phase,
physical defect and first-exit composition remains separate. -/
namespace GNC.OrbitalComparison.LieRadiusData
open LieRadiusPolynomial ParameterPolynomial Set

theorem z_bound {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ)) (ht : 0≤t) :
    ‖DiskPolynomial.vectorValue (input.z) ![θ,0,0] t‖≤
      PolynomialOrder.value (z.bound 0) t := by
  apply CoefficientNormProfile.certifies z (input.z) z_checked
  · change θ^2+(0:ℝ)^2≤((7/20:ℚ):ℝ)^2
    have hsq := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    norm_num [sq_abs] at hsq ⊢
    exact hsq
  · norm_num [Matrix.cons_val_two]
  · exact ht

theorem z_quadratic {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖DiskPolynomial.vectorValue (input.z) ![θ,0,0] t‖≤
      t^2*PolynomialOrder.value (z.bound 0) 1 := by
  exact (z_bound hθ ht.1).trans
    (PolynomialOrder.quadratic_time_bound _ (by decide +kernel) (by decide +kernel) ht)


theorem h_bound {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ)) (ht : 0≤t) :
    ‖DiskPolynomial.vectorValue (![input.h]) ![θ,0,0] t‖≤
      PolynomialOrder.value (h.bound 0) t := by
  apply CoefficientNormProfile.certifies h (![input.h]) h_checked
  · change θ^2+(0:ℝ)^2≤((7/20:ℚ):ℝ)^2
    have hsq := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    norm_num [sq_abs] at hsq ⊢
    exact hsq
  · norm_num [Matrix.cons_val_two]
  · exact ht

theorem h_quadratic {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖DiskPolynomial.vectorValue (![input.h]) ![θ,0,0] t‖≤
      t^2*PolynomialOrder.value (h.bound 0) 1 := by
  exact (h_bound hθ ht.1).trans
    (PolynomialOrder.quadratic_time_bound _ (by decide +kernel) (by decide +kernel) ht)


theorem u_bound {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ)) (ht : 0≤t) :
    ‖DiskPolynomial.vectorValue (![input.radiusDeviation]) ![θ,0,0] t‖≤
      PolynomialOrder.value (u.bound 0) t := by
  apply CoefficientNormProfile.certifies u (![input.radiusDeviation]) u_checked
  · change θ^2+(0:ℝ)^2≤((7/20:ℚ):ℝ)^2
    have hsq := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    norm_num [sq_abs] at hsq ⊢
    exact hsq
  · norm_num [Matrix.cons_val_two]
  · exact ht

theorem u_quadratic {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ))
    (ht : t ∈ Icc (0:ℝ) 1) :
    ‖DiskPolynomial.vectorValue (![input.radiusDeviation]) ![θ,0,0] t‖≤
      t^2*PolynomialOrder.value (u.bound 0) 1 := by
  exact (u_bound hθ ht.1).trans
    (PolynomialOrder.quadratic_time_bound _ (by decide +kernel) (by decide +kernel) ht)


theorem constraint_linear_bound {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ)) (ht : 0≤t) :
    ‖DiskPolynomial.vectorValue (![input.constraintLinear]) ![θ,0,0] t‖≤
      PolynomialOrder.value (constraint_linear.bound 0) t := by
  apply CoefficientNormProfile.certifies constraint_linear (![input.constraintLinear]) constraint_linear_checked
  · change θ^2+(0:ℝ)^2≤((7/20:ℚ):ℝ)^2
    have hsq := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    norm_num [sq_abs] at hsq ⊢
    exact hsq
  · norm_num [Matrix.cons_val_two]
  · exact ht


theorem lie_residual_bound {θ t : ℝ} (hθ : |θ|≤(7/20:ℝ)) (ht : 0≤t) :
    ‖DiskPolynomial.vectorValue (input.residual) ![θ,0,0] t‖≤
      PolynomialOrder.value (lie_residual.bound 0) t := by
  apply CoefficientNormProfile.certifies lie_residual (input.residual) lie_residual_checked
  · change θ^2+(0:ℝ)^2≤((7/20:ℚ):ℝ)^2
    have hsq := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    norm_num [sq_abs] at hsq ⊢
    exact hsq
  · norm_num [Matrix.cons_val_two]
  · exact ht

end GNC.OrbitalComparison.LieRadiusData
