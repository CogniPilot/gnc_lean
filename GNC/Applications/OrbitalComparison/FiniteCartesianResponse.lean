import GNC.Applications.OrbitalComparison.FiniteCartesianData
import GNC.Applications.OrbitalComparison.FiniteCircularResponse
import GNC.Lie.RotationFeatureBounds

/-! Finite Cartesian responses for exact components and quadratic angle
features. Both use the same polynomial residual checker and physical reference
as the geometric candidate, including all three pointing-error axes. -/
noncomputable section
namespace GNC.OrbitalComparison.FiniteCartesianResponse
open Matrix Set PolynomialOrder LinearResponsePolynomial
open FiniteCartesianData (Variant)
open FiniteResponseData (gamma beta speed2 delta)
open FiniteCircularResponse (basis basis_norm polynomialReference matrixOperator matrix_basis
  matrix_model rate_squared rate_bound physical_scales reference_error)
open PoweredCircularLogTube (μ U angleRadius rate reference thrust)
open GeometricSTMPrediction (E force)
open RotationFeatureBounds

def matrix : Variant → Vec3 → Matrix (Fin 3) (Fin 3) ℝ
  | .components, φ => exactMatrix φ
  | .quadratic, φ => quadraticMatrix φ

def action (v : Variant) (φ : Vec3) : E →L[ℝ] E :=
  (Matrix.toLpLin 2 2 (matrix v φ)).toContinuousLinearMap

def features (v : Variant) (φ : Vec3) : Fin 6 → ℝ :=
  ![matrix v φ 0 0, matrix v φ 0 1, matrix v φ 1 0,
    matrix v φ 1 1, matrix v φ 2 0, matrix v φ 2 1]

theorem feature_bound (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius) (j : Fin 6) :
    |features v φ j|≤(FiniteCartesianData.featureRadii v j:ℝ) := by
  have hφ' : enorm φ≤(FiniteResponseData.theta:ℝ) := by
    simpa [FiniteResponseData.theta, angleRadius] using hφ
  have hθ : (FiniteResponseData.theta:ℝ)<2*Real.pi := by
    norm_num [FiniteResponseData.theta]
    linarith [Real.pi_gt_three]
  cases v <;> fin_cases j <;>
    norm_num only [features, matrix, FiniteCartesianData.featureRadii, FiniteCartesianData.featureGain,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] <;>
    first | exact exact_diagonal φ _ hφ' | exact exact_entry φ _ _ hφ' hθ |
      exact quadratic_diagonal φ _ hφ' | exact quadratic_entry φ _ _ hφ'

theorem action_bound (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius) (u : E) :
    ‖action v φ u‖≤(FiniteCartesianData.featureGain v:ℝ)*‖u‖ := by
  have hφ' : enorm φ≤(FiniteResponseData.theta:ℝ) := by
    simpa [FiniteResponseData.theta, angleRadius] using hφ
  have hθ : (FiniteResponseData.theta:ℝ)<2*Real.pi := by
    norm_num [FiniteResponseData.theta]
    linarith [Real.pi_gt_three]
  cases v with
  | components => exact exact_norm φ u.ofLp hφ' hθ
  | quadratic => simpa only [FiniteCartesianData.featureGain, Rat.cast_add, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat] using quadratic_norm φ u.ofLp hφ'

private theorem value_nil (s : ℝ) : value [] s=0 := by
  simp [value, Planning.PolynomialKernel.evaluate]

theorem forcing_model (v : Variant) (φ : Vec3) (s : ℝ) :
    response basis FiniteCartesianData.forcing (features v φ) s=
      action v φ ((beta:ℝ) • polynomialReference s) := by
  ext i
  fin_cases i <;> simp [response, basis, FiniteCartesianData.forcing, features, action,
    Matrix.toLpLin_apply, polynomialReference, mulVec, dotProduct, Fin.sum_univ_succ,
    PolynomialOrder.value_scale, value_nil] <;> ring

def position (v : Variant) (φ : Vec3) (t : ℝ) : E :=
  response basis FiniteCartesianData.coefficients (features v φ) (rate*t)
def velocity (v : Variant) (φ : Vec3) (t : ℝ) : E :=
  LinearResponsePolynomial.velocity basis FiniteCartesianData.coefficients (features v φ) rate t
def acceleration (v : Variant) (φ : Vec3) (t : ℝ) : E :=
  LinearResponsePolynomial.acceleration basis FiniteCartesianData.coefficients (features v φ) rate t

theorem position_derivative (v : Variant) (φ : Vec3) (t : ℝ) :
    HasDerivAt (position v φ) (velocity v φ t) t :=
  response_derivative basis FiniteCartesianData.coefficients (features v φ) rate t

theorem velocity_derivative (v : Variant) (φ : Vec3) (t : ℝ) :
    HasDerivAt (velocity v φ) (acceleration v φ t) t :=
  LinearResponsePolynomial.velocity_derivative basis FiniteCartesianData.coefficients (features v φ) rate t

theorem position_bound (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖position v φ t‖≤(FiniteCartesianData.radius v:ℝ)*t^2 :=
  response_bound basis basis_norm FiniteCartesianData.coefficients (features v φ)
    (FiniteCartesianData.featureRadii v) (feature_bound v φ hφ)
    2 FiniteCartesianData.initial_zeros FiniteResponseData.inputs.2.2.2.2.1 rate_bound ht

theorem polynomial_defect (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖rate^2 • (Gravity.unitGradient (gamma:ℝ) (polynomialReference (rate*t)) (position v φ t)+
      action v φ ((beta:ℝ) • polynomialReference (rate*t))) - acceleration v φ t‖ ≤
      (speed2:ℝ)*(FiniteCartesianData.polynomialError v:ℝ)*t^7 := by
  simpa only [matrix_model, forcing_model, rate_squared] using
    defect_bound basis basis_norm FiniteCartesianData.coefficients FiniteCartesianData.forcing
      FiniteResponseData.gradient (features v φ) matrixOperator matrix_basis
      (FiniteCartesianData.featureRadii v) (feature_bound v φ hφ) 7 FiniteCartesianData.defect_zeros
      FiniteResponseData.inputs.2.2.2.2.1 rate_bound ht

theorem scaled_model (v : Variant) (φ : Vec3) (q y : E) :
    rate^2 • (Gravity.unitGradient (gamma:ℝ) q y+action v φ ((beta:ℝ) • q)) =
      Gravity.unitGradient μ q y+action v φ (U • q) := by
  rw [smul_add, Gravity.unitGradient, smul_smul, rate_squared, physical_scales.1]
  congr 1
  rw [←map_smul, smul_smul, physical_scales.2]

theorem residual_bound (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖Gravity.gradient μ (reference t) (position v φ t)+action v φ (thrust t)-
      acceleration v φ t‖≤(FiniteCartesianData.error v:ℝ)*t^7 := by
  let d : ℝ := delta
  let P : ℝ := FiniteCartesianData.radius v
  let α : ℝ := FiniteCartesianData.featureGain v
  have hd : 0≤d := by dsimp [d]; exact_mod_cast FiniteResponseData.inputs.2.2.2.2.2.2.2
  have hP : 0≤P := by dsimp [P]; exact_mod_cast (FiniteCartesianData.nonnegative v).2.1
  have hα : 0≤α := by dsimp [α]; exact_mod_cast (FiniteCartesianData.nonnegative v).1
  have hU := PoweredCircularLogTube.U_nonneg
  have hμ := PoweredCircularLogTube.μ_nonneg
  have ht0 := ht.1
  have ht17 : t^17≤1 := pow_le_one₀ ht.1 ht.2
  have ht7 : t^17≤t^7 := pow_le_pow_of_le_one ht.1 ht.2 (by norm_num : 7≤17)
  have hy : ‖position v φ t‖≤P := (position_bound v φ hφ ht).trans
    (mul_le_of_le_one_right hP (pow_le_one₀ ht.1 ht.2))
  have hq := reference_error ht
  have hgrad := Gravity.gradient_unit_approximation μ hμ (reference t)
    (polynomialReference (rate*t)) (position v φ t) (PoweredCircularLogTube.reference_norm t) hq
  have hg : ‖Gravity.gradient μ (reference t) (position v φ t)-
      Gravity.unitGradient μ (polynomialReference (rate*t)) (position v φ t)‖ ≤
      (3*μ*(2*d)*(2+2*d)*P)*t^7 := by
    calc
      _ ≤ 3*μ*(2*d*t^17)*(2+2*d*t^17)*‖position v φ t‖ := hgrad
      _ ≤ 3*μ*(2*d*t^17)*(2+2*d)*P := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_of_le_one_right (by positivity : 0≤2*d) ht17) 2)
          (by positivity)) hy (norm_nonneg _) (by positivity)
      _ = (3*μ*(2*d)*(2+2*d)*P)*t^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht7 (by positivity)
  have hf : ‖action v φ (U • reference t)-action v φ (U • polynomialReference (rate*t))‖ ≤
      (2*α*U*d)*t^7 := by
    rw [←map_sub, ←smul_sub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hU]
    calc
      _ ≤ U*(α*(2*d*t^17)) := mul_le_mul_of_nonneg_left
        ((action_bound v φ hφ _).trans (mul_le_mul_of_nonneg_left hq hα)) hU
      _ = (2*α*U*d)*t^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht7 (by positivity)
  have hp := polynomial_defect v φ hφ ht
  rw [scaled_model] at hp
  have he : Gravity.gradient μ (reference t) (position v φ t)+action v φ (thrust t)-acceleration v φ t=
      (Gravity.gradient μ (reference t) (position v φ t)-Gravity.unitGradient μ (polynomialReference (rate*t)) (position v φ t))+
      (action v φ (U • reference t)-action v φ (U • polynomialReference (rate*t)))+
      (Gravity.unitGradient μ (polynomialReference (rate*t)) (position v φ t)+
        action v φ (U • polynomialReference (rate*t))-acceleration v φ t) := by
    unfold thrust
    abel
  rw [he]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hg hf)) hp)).trans_eq ?_
  rw [←physical_scales.1, ←physical_scales.2]
  dsimp [d, P, α, FiniteCartesianData.error, FiniteCartesianData.trigError]
  push_cast
  ring

theorem position_initial (v : Variant) (φ : Vec3) : position v φ 0=0 := by
  simp [position, response, FiniteCartesianData.coefficients, PolynomialOrder.value,
    Planning.PolynomialKernel.evaluate, Fin.sum_univ_succ]

theorem velocity_initial (v : Variant) (φ : Vec3) : velocity v φ 0=0 := by
  simp [velocity, LinearResponsePolynomial.velocity, response, FiniteCartesianData.coefficients,
    PolynomialOrder.value, Planning.PolynomialKernel.evaluate, Planning.PolynomialKernel.differentiate,
    Planning.PolynomialKernel.weighted, Fin.sum_univ_succ]


/-- Charge the approximation of rotation features separately from time
polynomial truncation; the exact-component variant has zero input defect. -/
theorem force_error (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius) (t : ℝ) :
    ‖force φ (thrust t)-thrust t-action v φ (thrust t)‖≤(FiniteCartesianData.inputError v:ℝ) := by
  cases v with
  | components =>
    change enorm (rotate (rotationExp φ) (thrust t).ofLp-(thrust t).ofLp-
      exactMatrix φ *ᵥ (thrust t).ofLp)≤_
    rw [exact_apply]
    simp [FiniteCartesianData.inputError, enorm]
  | quadratic =>
    have h := quadratic_remainder φ (thrust t).ofLp hφ
    have hU : enorm (thrust t).ofLp=U := PoweredCircularLogTube.thrust_norm t
    rw [hU, sub_mulVec, exact_apply] at h
    change enorm (rotate (rotationExp φ) (thrust t).ofLp-(thrust t).ofLp-
      quadraticMatrix φ *ᵥ (thrust t).ofLp)≤_
    refine h.trans_eq ?_
    norm_num [FiniteCartesianData.inputError, FiniteResponseData.reconstructionTail,
      FiniteResponseData.theta, FiniteResponseData.thrust, JacobianAffine.tail, LieRadiusQuadratic.tail,
      PoweredCircularLogTube.angleRadius, PoweredCircularLogTube.U,
      PoweredCircularLogTube.physicalAcceleration, PoweredCircularLogTube.duration,
      PoweredCircularLogTube.lengthScale]

theorem physical_residual (v : Variant) (φ : Vec3) (hφ : enorm φ≤angleRadius)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖Gravity.gradient μ (reference t) (position v φ t)+(force φ (thrust t)-thrust t)-
      acceleration v φ t‖≤(FiniteCartesianData.inputError v:ℝ)+(FiniteCartesianData.error v:ℝ)*t^7 := by
  have he : Gravity.gradient μ (reference t) (position v φ t)+(force φ (thrust t)-thrust t)-acceleration v φ t=
      (Gravity.gradient μ (reference t) (position v φ t)+action v φ (thrust t)-acceleration v φ t)+
      (force φ (thrust t)-thrust t-action v φ (thrust t)) := by abel
  rw [he]
  simpa only [add_comm] using (norm_add_le _ _).trans
    (add_le_add (residual_bound v φ hφ ht) (force_error v φ hφ t))

end GNC.OrbitalComparison.FiniteCartesianResponse
