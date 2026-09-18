import GNC.Applications.OrbitalComparison.CenteredResponseAssembly

/-! Actual assembled response equations and their reference-transfer budgets.
The forcing-mismatch hypothesis is explicit until the rotation family is
substituted; coefficient residuals are fully checked, not assumed. -/
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set

def curve (p : Vector) (t : ℝ) : E3 := WithLp.toLp 2 (value p t)
def response {n : ℕ} (p : Fin n → Vector) (w : Fin n → ℝ) (t : ℝ) : E3 :=
  ∑ j, w j • curve (p j) t

theorem response_value {n : ℕ} (p : Fin n → Vector) (w : Fin n → ℝ) (t : ℝ) :
    response p w t=WithLp.toLp 2 (combination p w t) := by
  simp only [response,combination,curve,WithLp.toLp_sum,WithLp.toLp_smul]

theorem curve_derivative (p : Vector) (t : ℝ) :
    HasDerivAt (curve p) (curve (derivative p) t) t := by
  have he (p : Vector) (t : ℝ) : curve p t=SpatialBurn.pack
      (PolynomialOrder.value (p 0) t) (PolynomialOrder.value (p 1) t)
      (PolynomialOrder.value (p 2) t) := by
    rw [SpatialBurn.pack_eq]
    ext i
    fin_cases i <;> rfl
  change HasDerivAt (fun s => curve p s) _ t
  simp_rw [he]
  simpa only [SpatialBurn.pack,derivative] using
    (((PolynomialOrder.value_derivative (p 0) t).smul_const SpatialBurn.e0).add
      ((PolynomialOrder.value_derivative (p 1) t).smul_const SpatialBurn.e1)).add
      ((PolynomialOrder.value_derivative (p 2) t).smul_const SpatialBurn.e2)

theorem response_derivative {n : ℕ} (p : Fin n → Vector) (w : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (response p w) (response (fun j => derivative (p j)) w t) t := by
  exact HasDerivAt.fun_sum (fun j _ => (curve_derivative (p j) t).const_smul (w j))

theorem curve_gradient (k : ℚ) (q y : Vector) (t : ℝ) :
    curve (gradient k q y) t=Gravity.unitGradient (k:ℝ) (curve q t) (curve y t) := by
  simp only [curve,gradient_value,Gravity.unitGradient,Gravity.inner_toLp,
    WithLp.toLp_smul,WithLp.toLp_sub]

theorem curve_hessian (k c : ℚ) (q y z : Vector) (t : ℝ) :
    curve (hessian k c q y z) t=
      (c:ℝ) • Gravity.unitHessian (k:ℝ) (curve q t) (curve y t) (curve z t) := by
  simp only [curve,hessian_value,Gravity.unitHessian,Gravity.inner_toLp,
    WithLp.toLp_smul,WithLp.toLp_add]
  module

theorem curve_linear_residual (k : ℚ) (q y f : Vector) (t : ℝ) :
    curve (linearResidual k q y f) t=curve (derivative (derivative y)) t-
      (Gravity.unitGradient (k:ℝ) (curve q t) (curve y t)+curve f t) := by
  change WithLp.toLp 2 (value (linearResidual k q y f) t)=_
  rw [linearResidual,value_subtract,value_add,WithLp.toLp_sub,WithLp.toLp_add]
  exact congrArg (fun a => curve (derivative (derivative y)) t-(a+curve f t))
    (curve_gradient k q y t)

theorem curve_quadratic_residual (k c : ℚ) (q y z r : Vector) (t : ℝ) :
    curve (quadraticResidual k c q y z r) t=curve (derivative (derivative r)) t-
      (Gravity.unitGradient (k:ℝ) (curve q t) (curve r t)+
        (c:ℝ) • Gravity.unitHessian (k:ℝ) (curve q t) (curve y t) (curve z t)) := by
  change WithLp.toLp 2 (value (quadraticResidual k c q y z r) t)=_
  rw [quadraticResidual,value_subtract,value_add,WithLp.toLp_sub,WithLp.toLp_add]
  change curve (derivative (derivative r)) t-
      (curve (gradient k q r) t+curve (hessian k c q y z) t)=_
  rw [curve_gradient,curve_hessian]

def firstAcceleration (w : Fin 8 → ℝ) (t : ℝ) : E3 :=
  response (fun j => derivative (derivative (first j))) w t
def secondAcceleration (w : Fin 8 → ℝ) (t : ℝ) : E3 :=
  response (fun j => derivative (derivative (second j))) (productWeights w) t

theorem first_response_value (w : Fin 8 → ℝ) (t : ℝ) :
    firstResponse w t=response first w t := (response_value first w t).symm
theorem second_response_value (w : Fin 8 → ℝ) (t : ℝ) :
    secondResponse w t=response second (productWeights w) t :=
  (response_value second (productWeights w) t).symm

theorem linear_assembly (w : Fin 8 → ℝ) (t : ℝ) :
    response (fun j => linearResidual K reference (first j) (sources j)) w t=
      firstAcceleration w t-(Gravity.unitGradient (K:ℝ) (polynomialNominal t)
        (firstResponse w t)+response sources w t) := by
  rw [first_response_value]
  simp only [response,curve_linear_residual,unit_gradient_sum,unit_gradient_smul,
    firstAcceleration,smul_sub,smul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rfl

theorem quadratic_assembly (w : Fin 8 → ℝ) (t : ℝ) :
    response (fun j => quadraticResidual K (factor j) reference
      (first (pairLeft j)) (first (pairRight j)) (second j)) (productWeights w) t=
      secondAcceleration w t-(Gravity.unitGradient (K:ℝ) (polynomialNominal t)
        (secondResponse w t)+(1/2:ℝ) • Gravity.unitHessian (K:ℝ) (polynomialNominal t)
          (firstResponse w t) (firstResponse w t)) := by
  rw [first_response_value,second_response_value]
  simp only [response,curve_quadratic_residual,unit_gradient_sum,unit_gradient_smul,
    secondAcceleration,smul_sub,smul_add,smul_smul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [unordered_hessian_sum (K:ℝ) (curve reference t) (fun j => curve (first j) t) w]
  rfl

theorem first_surrogate_defect (w : Fin 8 → ℝ) (hw : ∀ j, |w j|≤1/20)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖firstAcceleration w t-(Gravity.unitGradient (K:ℝ) (polynomialNominal t)
      (firstResponse w t)+response sources w t)‖≤(linearDefect:ℝ) := by
  rw [←linear_assembly,response_value]
  exact combined_linear_residual w hw ht

theorem second_surrogate_defect (w : Fin 8 → ℝ) (hw : ∀ j, |w j|≤1/20)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondAcceleration w t-(Gravity.unitGradient (K:ℝ) (polynomialNominal t)
      (secondResponse w t)+(1/2:ℝ) • Gravity.unitHessian (K:ℝ) (polynomialNominal t)
        (firstResponse w t) (firstResponse w t))‖≤(quadraticDefect:ℝ) := by
  rw [←quadratic_assembly,response_value]
  exact combined_quadratic_residual w hw ht

end GNC.OrbitalComparison.CenteredResponseData
