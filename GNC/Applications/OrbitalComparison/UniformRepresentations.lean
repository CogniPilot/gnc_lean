import GNC.Applications.OrbitalComparison.UniformCertificate
import GNC.Analysis.CirclePolynomial
import GNC.Analysis.TrigonometricPolynomial

/-! Two coefficient algebras for the same finite-burn certificate.
The rotation-circle representation retains sine and cosine exactly. The
ordinary time/angle polynomial pays a proved order-16 source remainder.
Neither representation assumes that its candidate solves an approximate ODE:
the checker differentiates the stored coefficients and bounds the defect.
-/
namespace GNC.OrbitalComparison.UniformCertificate
noncomputable section

def circleRepresentation : Representation CirclePolynomial.Coefficients where
  add := CirclePolynomial.add
  multiply := CirclePolynomial.multiply
  scale := CirclePolynomial.scale
  derivative := CirclePolynomial.derivative
  bound := fun p h => CirclePolynomial.bound p h angle
  value := CirclePolynomial.value
  sine := ⟨[],[[1]]⟩
  cosineDifference := ⟨[[0,1]],[]⟩
  sourceError := 0
  value_add := CirclePolynomial.value_add
  value_multiply := CirclePolynomial.value_multiply
  value_scale := CirclePolynomial.value_scale
  value_derivative := CirclePolynomial.value_derivative
  bound_sound := fun p {_} {_ _} ht hθ => CirclePolynomial.bound_sound p ht hθ
  sine_error := by
    intros
    norm_num [CirclePolynomial.value,BivariatePolynomial.value,BivariatePolynomial.slice,
      BivariatePolynomial.row,Planning.PolynomialKernel.evaluate]
  cosine_error := by
    intros
    norm_num [CirclePolynomial.value,BivariatePolynomial.value,BivariatePolynomial.slice,
      BivariatePolynomial.row,Planning.PolynomialKernel.evaluate]

def trigonometricRemainder : ℚ := angle^17/355687428096000

theorem trigonometricRemainder_bound {θ : ℝ} (hθ : |θ| ≤ (angle:ℝ)) :
    |θ|^17/355687428096000 ≤ (trigonometricRemainder:ℝ) := by
  simp only [trigonometricRemainder,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg θ) hθ 17) (by norm_num)

def polynomialRepresentation : Representation BivariatePolynomial.Coefficients where
  add := BivariatePolynomial.add
  multiply := BivariatePolynomial.multiply
  scale := BivariatePolynomial.scale
  derivative := BivariatePolynomial.derivative
  bound := fun p h => BivariatePolynomial.bound p h angle
  value := BivariatePolynomial.value
  sine := [TrigonometricPolynomial.sine]
  cosineDifference := BivariatePolynomial.subtract [[1]] [TrigonometricPolynomial.cosine]
  sourceError := trigonometricRemainder
  value_add := BivariatePolynomial.value_add
  value_multiply := BivariatePolynomial.value_multiply
  value_scale := BivariatePolynomial.value_scale
  value_derivative := BivariatePolynomial.value_derivative
  bound_sound := fun p {_} {_ _} ht hθ => BivariatePolynomial.bound_sound p ht hθ
  sine_error := by
    intro t θ hθ
    have h := (TrigonometricPolynomial.sine_bound θ).trans (trigonometricRemainder_bound hθ)
    simpa [BivariatePolynomial.value,BivariatePolynomial.slice,
      Planning.PolynomialKernel.evaluate] using h
  cosine_error := by
    intro t θ hθ
    have h := (TrigonometricPolynomial.cosine_bound θ).trans (trigonometricRemainder_bound hθ)
    rw [BivariatePolynomial.value_subtract]
    have he : BivariatePolynomial.value [[1]] t θ = 1 := by
      norm_num [BivariatePolynomial.value,BivariatePolynomial.slice,
        BivariatePolynomial.row,Planning.PolynomialKernel.evaluate]
    have hc : BivariatePolynomial.value [TrigonometricPolynomial.cosine] t θ =
        BivariatePolynomial.row TrigonometricPolynomial.cosine θ := by
      simp [BivariatePolynomial.value,BivariatePolynomial.slice,
        Planning.PolynomialKernel.evaluate]
    rw [he,hc,show 1-Real.cos θ-(1-BivariatePolynomial.row TrigonometricPolynomial.cosine θ) =
      -(Real.cos θ-BivariatePolynomial.row TrigonometricPolynomial.cosine θ) by ring,abs_neg]
    exact h

end
end GNC.OrbitalComparison.UniformCertificate
