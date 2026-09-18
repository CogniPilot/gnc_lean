import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.BigOperators

/-! Restriction of a multivariate polynomial to a line through the origin.
The degree bound is inherited from mathlib, independently of the fitting
or tensor-compression procedure used to construct the polynomial. -/
noncomputable section
namespace GNC.PolynomialLine
variable {σ R : Type*} [CommSemiring R]

def restrict (v : σ → R) (p : MvPolynomial σ R) : Polynomial R :=
  ∑ m ∈ p.support, Polynomial.C (p.coeff m * m.prod (fun i e => v i ^ e)) *
    Polynomial.X ^ (m.sum fun _ e => e)

theorem degree (v : σ → R) (p : MvPolynomial σ R) :
    (restrict v p).natDegree ≤ p.totalDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (MvPolynomial.le_totalDegree hm)

theorem eval (v : σ → R) (p : MvPolynomial σ R) (t : R) :
    (restrict v p).eval t = MvPolynomial.eval (fun i => v i * t) p := by
  classical
  simp only [restrict, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, mul_assoc]

end GNC.PolynomialLine
