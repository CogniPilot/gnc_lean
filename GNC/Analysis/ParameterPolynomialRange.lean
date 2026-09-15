import GNC.Analysis.ParameterPolynomial

/-! Reuse kernel-checked scalar polynomial ranges when assembling a sparse
parameter-polynomial bound. This changes only proof evaluation: the result
is exactly `bound`, with the same Bernstein checks and rational arithmetic. -/
namespace GNC.ParameterPolynomial

/-- Sum supplied scalar ranges with the original parameter monomials.
`bound_eq_rangeSum` requires a matching checked range for every term. -/
def rangeSum : Coefficients → List ℚ → (Fin 3 → ℚ) → ℚ
  | [],_,_ => 0
  | _::_,[],_ => 0
  | a::p,b::bs,r => b*r 0^a.u*r 1^a.v*r 2^a.c+rangeSum p bs r

theorem bound_eq_rangeSum {p : Coefficients} {bs : List ℚ}
    (h : List.Forall₂ (fun a b => BernsteinPolynomial.checked a.time 0 1=b) p bs)
    (r : Fin 3 → ℚ) : bound p r=rangeSum p bs r := by
  induction h with
  | nil => rfl
  | @cons a b p bs hab h ih =>
    simp only [bound,List.map_cons,List.sum_cons] at *
    rw [rangeSum,hab,ih]

end GNC.ParameterPolynomial
