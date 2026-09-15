import GNC.Analysis.BivariatePolynomial

/-! The exact mathlib polynomial in the parameter at a fixed time.
Coefficient-list width gives its degree bound; numerical fitting and
coefficient choice are irrelevant to this representation theorem. -/
noncomputable section
namespace GNC.BivariateDegree
open Planning.PolynomialKernel BivariatePolynomial

theorem list_degree (a : List ℝ) : (polynomial a).natDegree ≤ a.length-1 := by
  induction a with
  | nil => simp [polynomial]
  | cons a p ih =>
    cases p with
    | nil => simp [polynomial]
    | cons b p =>
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · have h : ((Polynomial.X:Polynomial ℝ)*polynomial (b::p)).natDegree ≤
            (Polynomial.X:Polynomial ℝ).natDegree+(polynomial (b::p)).natDegree :=
          Polynomial.natDegree_mul_le
        simp only [Polynomial.natDegree_X,List.length_cons] at h ih ⊢
        omega

def atTime : BivariatePolynomial.Coefficients → ℝ → Polynomial ℝ
  | [],_ => 0
  | a::p,t => polynomial (a.map (Rat.castHom ℝ))+Polynomial.C t*atTime p t

theorem evaluation (p : BivariatePolynomial.Coefficients) (t θ : ℝ) :
    (atTime p t).eval θ = BivariatePolynomial.value p t θ := by
  induction p with
  | nil => simp [atTime,BivariatePolynomial.value,slice,evaluate]
  | cons a p ih =>
    change (polynomial (a.map (Rat.castHom ℝ))+Polynomial.C t*atTime p t).eval θ =
      row a θ+t*BivariatePolynomial.value p t θ
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,ih,row,evaluate_correct]

theorem degree (p : BivariatePolynomial.Coefficients) {d : ℕ}
    (hp : ∀ a ∈ p, a.length ≤ d+1) (t : ℝ) : (atTime p t).natDegree ≤ d := by
  induction p with
  | nil => simp [atTime]
  | cons a p ih =>
    have ha := hp a (by simp)
    have hrest := ih (fun b hb => hp b (by simp [hb]))
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · have h := list_degree (a.map (Rat.castHom ℝ))
      simp only [List.length_map] at h
      omega
    · exact (Polynomial.natDegree_C_mul_le t (atTime p t)).trans hrest

end GNC.BivariateDegree
