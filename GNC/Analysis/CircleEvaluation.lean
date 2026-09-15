import GNC.Analysis.CircleQuery
import GNC.Analysis.PolynomialEvaluation
import GNC.Analysis.TrigonometricPolynomial

/-! Certified point evaluation of the retained-angle representation. Exact
rational Horner evaluation is combined with mathlib-derived trigonometric
remainders. This supplies a checked point witness, rather than a floating
sample, when comparing a stored ordinary polynomial with a circle polynomial. -/
namespace GNC.CircleEvaluation
open Planning.PolynomialKernel PolynomialODE BivariatePolynomial

def rowExpr {n : ℕ} : List ℚ → Expr n → Expr n
  | [], _ => .constant 0
  | c :: cs, x => .add (.constant c) (.multiply x (rowExpr cs x))

theorem rowExpr_value {n : ℕ} (cs : List ℚ) (x : Expr n) (v : Fin n → ℝ) :
    (rowExpr cs x).value v = row cs (x.value v) := by
  induction cs with
  | nil => simp [rowExpr,Expr.value,row,evaluate]
  | cons c cs ih => simp [rowExpr,Expr.value,row,evaluate,ih]

theorem row_cast (cs : List ℚ) (q : ℚ) :
    row cs (q:ℝ) = ((evaluate cs q : ℚ):ℝ) := by
  exact evaluate_map (Rat.castHom ℝ) cs q

def polynomialValue (p : Coefficients) (t x : ℚ) : ℚ :=
  evaluate (atTime p t) x

theorem polynomialValue_cast (p : Coefficients) (t x : ℚ) :
    (polynomialValue p t x:ℝ) = value p (t:ℝ) (x:ℝ) := by
  rw [polynomialValue,← row_cast,row_atTime]

def expression (p : CirclePolynomial.Coefficients) (t : ℚ) : Expr 2 :=
  .add (rowExpr (atTime p.even t) (.var 1))
    (.multiply (.var 0) (rowExpr (atTime p.odd t) (.var 1)))

noncomputable def inputs (θ : ℝ) : Fin 2 → ℝ := ![Real.sin θ,1-Real.cos θ]

theorem expression_value (p : CirclePolynomial.Coefficients) (t : ℚ) (θ : ℝ) :
    (expression p t).value (inputs θ) = CirclePolynomial.value p (t:ℝ) θ := by
  simp only [expression,Expr.value,rowExpr_value,inputs,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,row_atTime,CirclePolynomial.value]

def center (q : ℚ) : Fin 2 → ℚ :=
  ![evaluate TrigonometricPolynomial.sine q,1-evaluate TrigonometricPolynomial.cosine q]

def radius (q : ℚ) : ℚ := |q|^17/355687428096000

theorem input_error (q : ℚ) (i : Fin 2) :
    |inputs (q:ℝ) i-(center q i:ℝ)| ≤ (radius q:ℝ) := by
  have hr : (radius q:ℝ) = |(q:ℝ)|^17/355687428096000 := by
    simp [radius]
  rw [hr]
  fin_cases i
  · simpa [inputs,center,row_cast] using TrigonometricPolynomial.sine_bound (q:ℝ)
  · have h := TrigonometricPolynomial.cosine_bound (q:ℝ)
    rw [row_cast] at h
    change |(1-Real.cos (q:ℝ))-((1-evaluate TrigonometricPolynomial.cosine q:ℚ):ℝ)| ≤ _
    push_cast
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1,h.2]

/-- The difference of the two relative predictions, including unit scaling.
The same computed nominal is subtracted within each representation. -/
def difference (p : CirclePolynomial.Coefficients) (q : Coefficients)
    (t angle scale : ℚ) : Expr 2 :=
  .add (.multiply (.constant scale) (expression (CircleQuery.relative p t) 0))
    (.constant (-scale*(polynomialValue q t angle-polynomialValue q t 0)))

theorem difference_value (p : CirclePolynomial.Coefficients) (q : Coefficients)
    (t angle scale : ℚ) :
    (difference p q t angle scale).value (inputs (angle:ℝ)) =
      (scale:ℝ)*((CirclePolynomial.value p (t:ℝ) (angle:ℝ)-
        CirclePolynomial.value p (t:ℝ) 0)-
        (value q (t:ℝ) (angle:ℝ)-value q (t:ℝ) 0)) := by
  simp only [difference,Expr.value,expression_value,CircleQuery.value_relative,
    Rat.cast_mul,Rat.cast_neg,Rat.cast_sub,polynomialValue_cast,Rat.cast_zero]
  ring

theorem difference_error (p : CirclePolynomial.Coefficients) (q : Coefficients)
    (t angle scale reported ε : ℚ) (M : Fin 2 → ℚ)
    (hM : ∀ i, 0 ≤ M i)
    (hregion : ∀ i, |center angle i|+radius angle ≤ M i)
    (hcertificate : (difference p q t angle scale).differenceMajorant M
        (fun _ => radius angle)+
      |(difference p q t angle scale).ratValue (center angle)-reported| ≤ ε) :
    |(scale:ℝ)*((CirclePolynomial.value p (t:ℝ) (angle:ℝ)-
        CirclePolynomial.value p (t:ℝ) 0)-
        (value q (t:ℝ) (angle:ℝ)-value q (t:ℝ) 0))-(reported:ℝ)| ≤ (ε:ℝ) := by
  have h := (difference p q t angle scale).rounded_evaluation_error
    (center angle) M (fun _ => radius angle) hM
    (fun _ => by unfold radius; positivity) hregion reported ε hcertificate
    (inputs (angle:ℝ)) (input_error angle)
  simpa only [difference_value] using h

end GNC.CircleEvaluation
