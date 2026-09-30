import GNC.Applications.OrbitalComparison.FiniteResponseData
import GNC.Applications.OrbitalComparison.PoweredCircularLogTube
import GNC.Dynamics.GravityUnitReferenceApproximation

/-! A degree-seven finite response for the powered circular example, with
its continuous-time differential residual checked from exact coefficients.
The whole three-dimensional pointing ball is covered, including zero. -/
noncomputable section
namespace GNC.OrbitalComparison.FiniteCircularResponse
open Set Matrix PolynomialOrder PolynomialBounds LinearResponsePolynomial
open GeometricSTMPrediction (E cross)
open PoweredCircularLogTube (rate reference μ U angleRadius)

open scoped RealInnerProductSpace

def basis (i : Fin 3) : E := PiLp.single 2 i 1

theorem basis_norm (i : Fin 3) : ‖basis i‖≤1 := by simp [basis]

def polynomialReference (s : ℝ) : E :=
  WithLp.toLp 2 ![value FiniteResponseData.c s, value FiniteResponseData.s s, 0]

def matrixOperator (s : ℝ) : E →L[ℝ] E :=
  (Matrix.toLpLin 2 2 (fun i j => value (FiniteResponseData.gradient i j) s)).toContinuousLinearMap

theorem matrix_basis (s : ℝ) (j : Fin 3) :
    matrixOperator s (basis j) = ∑ i, value (FiniteResponseData.gradient i j) s • basis i := by
  ext i
  simp [matrixOperator, basis, Matrix.toLpLin_apply, mulVec, dotProduct,
    Pi.single_apply]

private theorem value_nil (s : ℝ) : value [] s=0 := by simp [value, Planning.PolynomialKernel.evaluate]
private theorem value_single (a : ℚ) (s : ℝ) : value [a] s=a := by
  simp [value, Planning.PolynomialKernel.evaluate]

private theorem real_inner_product (a b : ℝ) : inner ℝ a b=a*b := by
  change b*a=a*b
  ring

theorem matrix_model (s : ℝ) (y : E) :
    matrixOperator s y=Gravity.unitGradient (FiniteResponseData.gamma:ℝ) (polynomialReference s) y := by
  ext i
  fin_cases i <;>
    simp [matrixOperator, Matrix.toLpLin_apply, mulVec, dotProduct,
      FiniteResponseData.gradient, Gravity.unitGradient, polynomialReference, PiLp.inner_apply, real_inner_product,
      Fin.sum_univ_succ, value_scale, value_add, value_product, value_nil, value_single] <;> ring

theorem forcing_model (φ : Vec3) (s : ℝ) :
    response basis FiniteResponseData.forcing φ s=cross φ ((FiniteResponseData.beta:ℝ) • polynomialReference s) := by
  ext i
  fin_cases i <;>
    simp [response, basis, FiniteResponseData.forcing, cross, polynomialReference, cross_apply,
      Fin.sum_univ_succ, value_scale, value_nil] <;> ring

def position (φ : Vec3) (t : ℝ) : E := response basis FiniteResponseData.coefficients φ (rate*t)
def velocity (φ : Vec3) (t : ℝ) : E := LinearResponsePolynomial.velocity basis FiniteResponseData.coefficients φ rate t
def acceleration (φ : Vec3) (t : ℝ) : E := LinearResponsePolynomial.acceleration basis FiniteResponseData.coefficients φ rate t

theorem position_derivative (φ : Vec3) (t : ℝ) : HasDerivAt (position φ) (velocity φ t) t :=
  response_derivative basis FiniteResponseData.coefficients φ rate t

theorem velocity_derivative (φ : Vec3) (t : ℝ) : HasDerivAt (velocity φ) (acceleration φ t) t :=
  LinearResponsePolynomial.velocity_derivative basis FiniteResponseData.coefficients φ rate t

theorem rate_squared : rate^2=(FiniteResponseData.speed2:ℝ) := by
  rw [PoweredCircularLogTube.rate_sq]
  norm_num [FiniteResponseData.speed2, FiniteResponseData.mu, FiniteResponseData.thrust, PoweredCircularLogTube.μ, PoweredCircularLogTube.U,
    PoweredCircularLogTube.earthMu, PoweredCircularLogTube.duration,
    PoweredCircularLogTube.lengthScale, PoweredCircularLogTube.physicalAcceleration]

theorem rate_bound : |rate|≤(FiniteResponseData.horizon:ℝ) := by
  have hh : (0:ℝ)≤FiniteResponseData.horizon := by exact_mod_cast FiniteResponseData.inputs.2.2.2.2.1
  have hs : (FiniteResponseData.speed2:ℝ)≤(FiniteResponseData.horizon:ℝ)^2 := by exact_mod_cast FiniteResponseData.inputs.2.2.2.2.2.2.1
  nlinarith [rate_squared, sq_abs rate, abs_nonneg rate]

theorem feature_bound (φ : Vec3) (hφ : enorm φ≤angleRadius) (j : Fin 3) :
    |φ j|≤(FiniteResponseData.theta:ℝ) := by
  exact (component_le_enorm φ j).trans (by simpa [FiniteResponseData.theta, angleRadius] using hφ)

theorem position_bound (φ : Vec3) (hφ : enorm φ≤angleRadius) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖position φ t‖≤(FiniteResponseData.radius:ℝ)*t^2 :=
  response_bound basis basis_norm FiniteResponseData.coefficients φ (fun _ => FiniteResponseData.theta) (feature_bound φ hφ)
    2 FiniteResponseData.initial_zeros FiniteResponseData.inputs.2.2.2.2.1 rate_bound ht

theorem polynomial_defect (φ : Vec3) (hφ : enorm φ≤angleRadius) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖rate^2 • (Gravity.unitGradient (FiniteResponseData.gamma:ℝ) (polynomialReference (rate*t)) (position φ t)+
      cross φ ((FiniteResponseData.beta:ℝ) • polynomialReference (rate*t))) - acceleration φ t‖ ≤
      (FiniteResponseData.speed2:ℝ)*(FiniteResponseData.polynomialError:ℝ)*t^6 := by
  simpa only [matrix_model, forcing_model, rate_squared] using
    defect_bound basis basis_norm FiniteResponseData.coefficients FiniteResponseData.forcing FiniteResponseData.gradient φ matrixOperator matrix_basis
      (fun _ => FiniteResponseData.theta) (feature_bound φ hφ) 6 FiniteResponseData.defect_zeros FiniteResponseData.inputs.2.2.2.2.1 rate_bound ht

/-- The polynomial reference's discrepancy is bounded on the entire burn.
It is not assumed to have unit length. -/
theorem reference_error {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖reference t-polynomialReference (rate*t)‖≤(2*(FiniteResponseData.delta:ℝ))*t^17 := by
  have hphase : |rate*t|^17/355687428096000≤(FiniteResponseData.delta:ℝ)*t^17 := by
    rw [abs_mul, abs_of_nonneg ht.1, mul_pow]
    calc
      _ ≤ ((FiniteResponseData.horizon:ℝ)^17*t^17)/355687428096000 := by
        have ht0 := ht.1
        gcongr
        exact rate_bound
      _ = _ := by simp [FiniteResponseData.delta]; ring
  have hc := (TrigonometricPolynomial.cosine_bound (rate*t)).trans hphase
  have hs := (TrigonometricPolynomial.sine_bound (rate*t)).trans hphase
  have he : reference t-polynomialReference (rate*t)=SpatialBurn.pack
      (Real.cos (rate*t)-value FiniteResponseData.c (rate*t)) (Real.sin (rate*t)-value FiniteResponseData.s (rate*t)) 0 := by
    ext i
    fin_cases i <;> simp [reference, polynomialReference, VaryingRateReference.position,
      SpatialRotatingFrame.mix, SpatialBurn.pack, SpatialBurn.e0, SpatialBurn.e1, SpatialBurn.e2]
  rw [he]
  have hp := SpatialBurn.pack_norm_le (Real.cos (rate*t)-value FiniteResponseData.c (rate*t))
    (Real.sin (rate*t)-value FiniteResponseData.s (rate*t)) 0
  change |Real.cos (rate*t)-value FiniteResponseData.c (rate*t)|≤_ at hc
  change |Real.sin (rate*t)-value FiniteResponseData.s (rate*t)|≤_ at hs
  simp only [abs_zero, add_zero] at hp
  exact hp.trans (by linarith)


theorem physical_scales : (FiniteResponseData.speed2:ℝ)*(FiniteResponseData.gamma:ℝ)=μ ∧
    (FiniteResponseData.speed2:ℝ)*(FiniteResponseData.beta:ℝ)=U := by
  norm_num [FiniteResponseData.speed2, FiniteResponseData.gamma, FiniteResponseData.beta,
    FiniteResponseData.mu, FiniteResponseData.thrust, PoweredCircularLogTube.μ,
    PoweredCircularLogTube.U, PoweredCircularLogTube.earthMu, PoweredCircularLogTube.duration,
    PoweredCircularLogTube.lengthScale, PoweredCircularLogTube.physicalAcceleration]

theorem scaled_model (φ : Vec3) (q y : E) :
    rate^2 • (Gravity.unitGradient (FiniteResponseData.gamma:ℝ) q y+
      cross φ ((FiniteResponseData.beta:ℝ) • q)) =
      Gravity.unitGradient μ q y+cross φ (U • q) := by
  rw [smul_add, Gravity.unitGradient, smul_smul, rate_squared, physical_scales.1]
  congr 1
  ext i
  fin_cases i <;> simp [cross, cross_apply] <;>
    simp only [←mul_assoc, physical_scales.2]

/-- End-to-end bound for the acceleration defect of the finite polynomial.
Both the coefficient residual and the analytic reference approximation are
charged. All inequalities hold throughout the burn and the attitude ball. -/
theorem residual_bound (φ : Vec3) (hφ : enorm φ≤angleRadius) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖Gravity.gradient μ (reference t) (position φ t)+cross φ (PoweredCircularLogTube.thrust t)-
      acceleration φ t‖≤(FiniteResponseData.error:ℝ)*t^6 := by
  let d : ℝ := FiniteResponseData.delta
  let P : ℝ := FiniteResponseData.radius
  have hd : 0≤d := by dsimp [d]; exact_mod_cast FiniteResponseData.inputs.2.2.2.2.2.2.2
  have hP : 0≤P := by dsimp [P]; exact_mod_cast FiniteResponseData.budgets_nonneg.1
  have hθ : 0≤angleRadius := by norm_num [angleRadius]
  have hU := PoweredCircularLogTube.U_nonneg
  have hμ := PoweredCircularLogTube.μ_nonneg
  have ht0 := ht.1
  have ht17 : t^17≤1 := pow_le_one₀ ht.1 ht.2
  have ht6 : t^17≤t^6 := pow_le_pow_of_le_one ht.1 ht.2 (by norm_num : 6≤17)
  have hy : ‖position φ t‖≤P := (position_bound φ hφ ht).trans
    (mul_le_of_le_one_right hP (pow_le_one₀ ht.1 ht.2))
  have hq := reference_error ht
  have hgrad := Gravity.gradient_unit_approximation μ hμ (reference t)
    (polynomialReference (rate*t)) (position φ t) (PoweredCircularLogTube.reference_norm t) hq
  have hg : ‖Gravity.gradient μ (reference t) (position φ t)-
      Gravity.unitGradient μ (polynomialReference (rate*t)) (position φ t)‖ ≤
      (3*μ*(2*d)*(2+2*d)*P)*t^6 := by
    calc
      _ ≤ 3*μ*(2*d*t^17)*(2+2*d*t^17)*‖position φ t‖ := hgrad
      _ ≤ 3*μ*(2*d*t^17)*(2+2*d)*P := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_of_le_one_right (by positivity : 0≤2*d) ht17) 2)
          (by positivity)) hy (norm_nonneg _) (by positivity)
      _ = (3*μ*(2*d)*(2+2*d)*P)*t^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht6 (by positivity)
  have hf : ‖cross φ (U • reference t)-cross φ (U • polynomialReference (rate*t))‖ ≤
      (2*angleRadius*U*d)*t^6 := by
    have he : cross φ (U • reference t)-cross φ (U • polynomialReference (rate*t))=
        U • cross φ (reference t-polynomialReference (rate*t)) := by
      ext i
      fin_cases i <;> simp [cross, cross_apply] <;> ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hU]
    have hn := cross_enorm_le φ (reference t-polynomialReference (rate*t)).ofLp
    change ‖cross φ (reference t-polynomialReference (rate*t))‖≤enorm φ*‖reference t-polynomialReference (rate*t)‖ at hn
    calc
      _ ≤ U*(angleRadius*(2*d*t^17)) := mul_le_mul_of_nonneg_left
        (hn.trans (mul_le_mul hφ hq (norm_nonneg _) hθ)) hU
      _ = (2*angleRadius*U*d)*t^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ht6 (by positivity)
  have hp := polynomial_defect φ hφ ht
  rw [scaled_model] at hp
  have he : Gravity.gradient μ (reference t) (position φ t)+cross φ (PoweredCircularLogTube.thrust t)-acceleration φ t=
      (Gravity.gradient μ (reference t) (position φ t)-Gravity.unitGradient μ (polynomialReference (rate*t)) (position φ t))+
      (cross φ (U • reference t)-cross φ (U • polynomialReference (rate*t)))+
      (Gravity.unitGradient μ (polynomialReference (rate*t)) (position φ t)+
        cross φ (U • polynomialReference (rate*t))-acceleration φ t) := by
    unfold PoweredCircularLogTube.thrust
    abel
  rw [he]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hg hf)) hp)).trans_eq ?_
  have hm := physical_scales.1
  have hu := physical_scales.2
  have htheta : angleRadius=(FiniteResponseData.theta:ℝ) := by norm_num [angleRadius, FiniteResponseData.theta]
  rw [←hm, ←hu, htheta]
  dsimp [d, P, FiniteResponseData.error, FiniteResponseData.trigError]
  push_cast
  ring

theorem position_initial (φ : Vec3) : position φ 0=0 := by
  simp [position, response, FiniteResponseData.coefficients, PolynomialOrder.value,
    Planning.PolynomialKernel.evaluate, Fin.sum_univ_succ]

theorem velocity_initial (φ : Vec3) : velocity φ 0=0 := by
  simp [velocity, LinearResponsePolynomial.velocity, response, FiniteResponseData.coefficients,
    PolynomialOrder.value, Planning.PolynomialKernel.evaluate, Planning.PolynomialKernel.differentiate,
    Planning.PolynomialKernel.weighted, Fin.sum_univ_succ]

end GNC.OrbitalComparison.FiniteCircularResponse
