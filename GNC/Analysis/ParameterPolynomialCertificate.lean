import GNC.Analysis.ParameterPolynomialEvaluation

/-! Exact weighted-square certificates for sparse parameter polynomials.
The producer may use any optimizer. Acceptance checks rational identities
and signs; neither the optimizer nor floating-point eigenvalues are trusted. -/
namespace GNC.ParameterPolynomial
open Planning.PolynomialKernel

def atTime (p : Coefficients) (t : ℚ) : Coefficients :=
  p.map fun a => {a with time := [evaluate a.time t]}

theorem value_atTime (p : Coefficients) (t : ℚ) (x : Fin 3 → ℝ) (s : ℝ) :
    value (atTime p t) x s = value p x (t:ℝ) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [atTime,List.map_cons,value_cons] at *
    rw [ih]
    simp [termValue,monomial,PolynomialOrder.value,
      evaluate,← PolynomialOrder.value_at_rational]

def weightedSquares : List (ℚ × Coefficients) → Coefficients
  | [] => []
  | (w,p)::rest => add (scale w (multiply p p)) (weightedSquares rest)

def NonnegativeWeights (rows : List (ℚ × Coefficients)) : Prop :=
  ∀ r ∈ rows, 0 ≤ r.1

instance (rows : List (ℚ × Coefficients)) : Decidable (NonnegativeWeights rows) := by
  unfold NonnegativeWeights
  infer_instance

theorem weightedSquares_nonnegative (rows : List (ℚ × Coefficients))
    (h : NonnegativeWeights rows) (x : Fin 3 → ℝ) (t : ℝ) :
    0 ≤ value (weightedSquares rows) x t := by
  induction rows with
  | nil => simp [weightedSquares]
  | cons r rows ih =>
    have hw : (0:ℝ) ≤ r.1 := by exact_mod_cast h r (by simp)
    have hr := ih (fun a ha => h a (by simp [ha]))
    simpa only [weightedSquares,value_add,value_scale,value_multiply] using
      add_nonneg (mul_nonneg hw (mul_self_nonneg (value r.2 x t))) hr

end GNC.ParameterPolynomial
