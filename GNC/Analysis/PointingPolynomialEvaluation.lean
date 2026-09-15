import GNC.Analysis.ParameterPolynomialEvaluation
import GNC.Analysis.CircleEvaluation

/-! Exact point evaluation of a sparse retained-pointing polynomial. The
only uncertain inputs are sine and cosine; their remainders are charged by
the existing polynomial expression evaluator. -/
namespace GNC.PointingPolynomialEvaluation
open ParameterPolynomial PolynomialODE Planning.PolynomialKernel

def power (e : Expr 2) : ℕ → Expr 2
  | 0 => .constant 1
  | n+1 => .multiply (power e n) e

theorem power_value (e : Expr 2) (n : ℕ) (x : Fin 2 → ℝ) :
    (power e n).value x=(e.value x)^n := by
  induction n with
  | zero => simp [power,Expr.value]
  | succ n ih => simp [power,Expr.value,ih,pow_succ]

def expression (p : Coefficients) (t : ℚ) : Expr 2 :=
  (p.map fun a => Expr.multiply
    (.multiply (.multiply (.constant (evaluate a.time t)) (power (.var 0) a.u))
      (power (.constant 0) a.v)) (power (.var 1) a.c)).foldr Expr.add (.constant 0)

theorem expression_value (p : Coefficients) (t : ℚ) (θ : ℝ) :
    (expression p t).value (CircleEvaluation.inputs θ)=
      ParameterPolynomial.value p ![Real.sin θ,0,1-Real.cos θ] (t:ℝ) := by
  induction p with
  | nil => simp [expression,Expr.value]
  | cons a p ih =>
    simp only [expression,List.map_cons,List.foldr_cons,Expr.value] at *
    rw [ih]
    simp [power_value,Expr.value,CircleEvaluation.inputs,ParameterPolynomial.termValue,
      ParameterPolynomial.monomial,PolynomialOrder.value_at_rational]
    <;> ring

end GNC.PointingPolynomialEvaluation
