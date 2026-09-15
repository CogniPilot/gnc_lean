import GNC.Analysis.ParameterPolynomial

/-! Exact rational point evaluation for sparse parameter/time polynomials.
The cast theorem connects executable arithmetic to the real semantics. -/
namespace GNC.ParameterPolynomial
open Planning.PolynomialKernel

def rationalValue (p : Coefficients) (x : Fin 3 → ℚ) (t : ℚ) : ℚ :=
  (p.map fun a => evaluate a.time t*x 0^a.u*x 1^a.v*x 2^a.c).sum

theorem rationalValue_cast (p : Coefficients) (x : Fin 3 → ℚ) (t : ℚ) :
    (rationalValue p x t:ℝ)=value p (fun i => (x i:ℝ)) (t:ℝ) := by
  induction p with
  | nil => simp [rationalValue]
  | cons a p ih =>
    simp only [rationalValue,List.map_cons,List.sum_cons,Rat.cast_add] at *
    rw [ih,value_cons]
    simp only [termValue,monomial,PolynomialOrder.value_at_rational,
      Rat.cast_mul,Rat.cast_pow]
    ring

end GNC.ParameterPolynomial
