import GNC.Analysis.PolynomialBox

/-! Exact evaluation of terminal polynomial expressions, with a proved error
budget for uncertain inputs and rational rounding of the reported output.
The expression may combine reference states, fundamental matrices, burn
integrals and unit conversions. Their input error bounds remain explicit.
-/
namespace GNC.PolynomialODE.Expr
variable {n : ℕ}

def ratValue (e : Expr n) (x : Fin n → ℚ) : ℚ :=
  match e with
  | constant c => c
  | var i => x i
  | add a b => a.ratValue x + b.ratValue x
  | multiply a b => a.ratValue x * b.ratValue x
  | negate a => -a.ratValue x

theorem ratValue_cast (e : Expr n) (x : Fin n → ℚ) :
    (e.ratValue x : ℝ) = e.value (fun i => (x i : ℝ)) := by
  induction e <;> simp_all [ratValue, value]

theorem evaluation_error (e : Expr n) (center M B : Fin n → ℚ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hregion : ∀ i, |center i|+B i ≤ M i)
    (x : Fin n → ℝ) (hx : ∀ i, |x i-(center i:ℝ)| ≤ (B i:ℝ)) :
    |e.value x-(e.ratValue center:ℝ)| ≤ (e.differenceMajorant M B:ℝ) := by
  rw [ratValue_cast]
  have hr (i) : |(center i:ℝ)|+(B i:ℝ) ≤ (M i:ℝ) := by
    exact_mod_cast hregion i
  apply e.box_difference_bound hM hB x (fun i => (center i:ℝ)) ?_ ?_ hx
  · intro i
    have ht := abs_add_le (x i-(center i:ℝ)) (center i:ℝ)
    have hi := hx i
    have hb := hr i
    simp only [sub_add_cancel] at ht
    linarith
  · intro i
    have hb : (0:ℝ) ≤ (B i:ℝ) := by exact_mod_cast hB i
    linarith [hr i]

/-- One exact rational inequality pays for both uncertain inputs and rounding.
Checking this inequality by kernel reduction certifies every real input in
the stated box; no floating-point expression evaluation is trusted. -/
theorem rounded_evaluation_error (e : Expr n) (center M B : Fin n → ℚ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hregion : ∀ i, |center i|+B i ≤ M i)
    (reported ε : ℚ)
    (hcertificate : e.differenceMajorant M B+|e.ratValue center-reported| ≤ ε)
    (x : Fin n → ℝ) (hx : ∀ i, |x i-(center i:ℝ)| ≤ (B i:ℝ)) :
    |e.value x-(reported:ℝ)| ≤ (ε:ℝ) := by
  have h := e.evaluation_error center M B hM hB hregion x hx
  have hc : (e.differenceMajorant M B:ℝ)+
      |(e.ratValue center:ℝ)-(reported:ℝ)| ≤ (ε:ℝ) := by
    exact_mod_cast hcertificate
  linarith [abs_sub_le (e.value x) (e.ratValue center:ℝ) (reported:ℝ)]

end GNC.PolynomialODE.Expr

namespace GNC.PolynomialEvaluation

/-- Square-root unit conversions can be enclosed using rational squared
endpoints and mathlib's actual real square root. -/
theorem sqrt_error {a center ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hlo : 0 ≤ center-ε) (hlower : (center-ε)^2 ≤ a)
    (hupper : a ≤ (center+ε)^2) : |Real.sqrt a-center| ≤ ε := by
  have hs := Real.sq_sqrt ha
  have hn := Real.sqrt_nonneg a
  apply abs_le.mpr
  constructor <;> nlinarith

end GNC.PolynomialEvaluation
