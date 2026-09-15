import GNC.Analysis.CirclePolynomial

/-! A finite-angle response quadratic in sin θ and 1-cos θ uses five
fixed angular functions after reduction by the exact circle relation.
This is a span statement, not a claim of independence or a FLOP lower bound. -/
noncomputable section
namespace GNC.FiniteAngleSpan
open BivariatePolynomial Planning.PolynomialKernel

def width (n : ℕ) (p : BivariatePolynomial.Coefficients) : Prop :=
  ∀ a ∈ p, a.length ≤ n

instance (n : ℕ) (p : BivariatePolynomial.Coefficients) : Decidable (width n p) := by
  unfold width
  infer_instance

def column (p : BivariatePolynomial.Coefficients) (j : ℕ) (t : ℝ) : ℝ :=
  evaluate (p.map (fun a => ((a[j]?.getD 0 : ℚ):ℝ))) t

theorem row_three (a : List ℚ) (h : a.length ≤ 3) (x : ℝ) :
    row a x = (a[0]?.getD 0:ℚ)+(a[1]?.getD 0:ℚ)*x+(a[2]?.getD 0:ℚ)*x^2 := by
  rcases a with _ | ⟨a,a'⟩
  · simp [row,evaluate]
  rcases a' with _ | ⟨b,b'⟩
  · simp [row,evaluate]
  rcases b' with _ | ⟨c,c'⟩
  · simp [row,evaluate]; ring
  have hc : c' = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_cons] at h
    omega
  subst c'
  simp [row,evaluate]
  ring

theorem row_two (a : List ℚ) (h : a.length ≤ 2) (x : ℝ) :
    row a x = (a[0]?.getD 0:ℚ)+(a[1]?.getD 0:ℚ)*x := by
  rcases a with _ | ⟨a,a'⟩
  · simp [row,evaluate]
  rcases a' with _ | ⟨b,b'⟩
  · simp [row,evaluate]
  have hb : b' = [] := by simpa using h
  subst b'
  simp [row,evaluate]
  ring

theorem value_three (p : BivariatePolynomial.Coefficients) (h : width 3 p) (t x : ℝ) :
    BivariatePolynomial.value p t x = column p 0 t+column p 1 t*x+column p 2 t*x^2 := by
  induction p with
  | nil => simp [BivariatePolynomial.value,slice,column,evaluate]
  | cons a p ih =>
    have ha : a.length ≤ 3 := h a (by simp)
    have hp : width 3 p := fun b hb => h b (by simp [hb])
    change row a x+t*BivariatePolynomial.value p t x = _
    rw [row_three a ha,ih hp]
    simp only [column,List.map_cons,evaluate]
    ring

theorem value_two (p : BivariatePolynomial.Coefficients) (h : width 2 p) (t x : ℝ) :
    BivariatePolynomial.value p t x = column p 0 t+column p 1 t*x := by
  induction p with
  | nil => simp [BivariatePolynomial.value,slice,column,evaluate]
  | cons a p ih =>
    have ha : a.length ≤ 2 := h a (by simp)
    have hp : width 2 p := fun b hb => h b (by simp [hb])
    change row a x+t*BivariatePolynomial.value p t x = _
    rw [row_two a ha,ih hp]
    simp only [column,List.map_cons,evaluate]
    ring

def quadratic (p : CirclePolynomial.Coefficients) : Prop := width 3 p.even ∧ width 2 p.odd

instance (p : CirclePolynomial.Coefficients) : Decidable (quadratic p) := by
  unfold quadratic
  infer_instance

def amplitudes (p : CirclePolynomial.Coefficients) (t : ℝ) : Fin 5 → ℝ :=
  ![column p.even 0 t,column p.odd 0 t,column p.even 1 t,column p.odd 1 t,column p.even 2 t]

theorem value_five (p : CirclePolynomial.Coefficients) (h : quadratic p) (t θ : ℝ) :
    CirclePolynomial.value p t θ =
      amplitudes p t 0+Real.sin θ*amplitudes p t 1+(1-Real.cos θ)*amplitudes p t 2+
      (Real.sin θ*(1-Real.cos θ))*amplitudes p t 3+(1-Real.cos θ)^2*amplitudes p t 4 := by
  rw [CirclePolynomial.value,value_three p.even h.1,value_two p.odd h.2]
  simp [amplitudes,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  ring

end GNC.FiniteAngleSpan
