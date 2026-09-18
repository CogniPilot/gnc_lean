import GNC.Analysis.BallPolynomialEnclosure
import GNC.Analysis.ParameterPolynomialCertificate
import GNC.Applications.OrbitalComparison.PointingCapPolynomial

/-! Polynomial coefficient queries retaining a directional tensor factorization.
Their range and residual can be checked without trusting an eigensolver or
ODE solver. The rank is kept in the executable expression, not inferred
from a nearly low-rank expanded polynomial. -/
namespace GNC.OrbitalComparison.TDSTTPolynomial
open ParameterPolynomial BallPolynomialEnclosure PointingCapPolynomial

structure Input (rank : ℕ) where
  first : Fin 7 → Fin 3 → List ℚ
  basis : Fin rank → Fin 3 → List ℚ
  tensor : Fin 7 → Fin rank → Fin rank → List ℚ

def time (p : List ℚ) : Coefficients := [⟨0,0,0,p⟩]
def parameter : Fin 3 → Coefficients := ![u,v,c]
def Input.feature {r : ℕ} (D : Input r) (a : Fin r) : Coefficients :=
  polynomialSum fun j => multiply (time (D.basis a j)) (parameter j)
def Input.query {r : ℕ} (D : Input r) (i : Fin 7) : Coefficients :=
  add (polynomialSum fun j => multiply (time (D.first i j)) (parameter j))
    (scale (1/2) (polynomialSum fun a => polynomialSum fun b =>
      multiply (time (D.tensor i a b)) (multiply (D.feature a) (D.feature b))))

noncomputable section

theorem time_value (p : List ℚ) (x : Fin 3 → ℝ) (t : ℝ) :
    value (time p) x t=PolynomialOrder.value p t := by
  simp [time,value,termValue,monomial]

theorem parameter_value (i : Fin 3) (x : Fin 3 → ℝ) (t : ℝ) :
    value (parameter i) x t=x i := by
  fin_cases i <;> simp [parameter]

theorem Input.feature_value {r : ℕ} (D : Input r) (a : Fin r)
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (D.feature a) x t=∑ j, PolynomialOrder.value (D.basis a j) t*x j := by
  simp only [Input.feature,polynomialSum_value,value_multiply,time_value,parameter_value]

/-- The delivered quadratic query keeps exactly the specified number of
directions, including for polynomial approximate directions. -/
theorem Input.query_value {r : ℕ} (D : Input r) (i : Fin 7)
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (D.query i) x t=
      (∑ j, PolynomialOrder.value (D.first i j) t*x j)+
        (1/2:ℝ)*(∑ a, ∑ b, PolynomialOrder.value (D.tensor i a b) t*
          ((∑ j, PolynomialOrder.value (D.basis a j) t*x j)*
           (∑ j, PolynomialOrder.value (D.basis b j) t*x j))) := by
  simp only [Input.query,value_add,polynomialSum_value,value_scale,value_multiply,
    time_value,parameter_value,Input.feature_value,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]

end
end GNC.OrbitalComparison.TDSTTPolynomial
