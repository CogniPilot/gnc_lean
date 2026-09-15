import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring

/-! Restricting a bivariate polynomial to its first coordinate axis.
The total-degree bound is inherited from mathlib's support/degree results. -/
noncomputable section
namespace GNC.PolynomialSlice
variable {R : Type*} [CommSemiring R]

def firstAxis (p : MvPolynomial (Fin 2) R) : Polynomial R :=
  ∑ m ∈ p.support, Polynomial.C (p.coeff m*(0:R)^(m 1))*Polynomial.X^(m 0)

theorem firstAxis_degree (p : MvPolynomial (Fin 2) R) :
    (firstAxis p).natDegree≤p.totalDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    ((MvPolynomial.monomial_le_degreeOf 0 hm).trans (MvPolynomial.degreeOf_le_totalDegree p 0))

theorem firstAxis_eval (p : MvPolynomial (Fin 2) R) (u : R) :
    (firstAxis p).eval u=MvPolynomial.eval ![u,0] p := by
  simp only [firstAxis,Polynomial.eval_finset_sum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro m _
  simp [Fin.prod_univ_succ]
  ring

end GNC.PolynomialSlice
