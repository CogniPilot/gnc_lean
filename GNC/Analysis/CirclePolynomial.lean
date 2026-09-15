import GNC.Analysis.BivariatePolynomial
import GNC.Analysis.FiniteAngleReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A finite-angle certificate algebra. Every expression is stored as
P(t,c)+s Q(t,c), with s=sin(theta), c=1-cos(theta). Multiplication reduces
s^2 to 2c-c^2 exactly. This preserves the rotation constraint instead of
independently boxing s and c or expanding the angle to high Taylor order.
-/
namespace GNC.CirclePolynomial

structure Coefficients where
  even : BivariatePolynomial.Coefficients
  odd : BivariatePolynomial.Coefficients
  deriving Repr

noncomputable def value (p : Coefficients) (t θ : ℝ) : ℝ :=
  BivariatePolynomial.value p.even t (1-Real.cos θ)+Real.sin θ*BivariatePolynomial.value p.odd t (1-Real.cos θ)

def add (p q : Coefficients) : Coefficients :=
  ⟨BivariatePolynomial.add p.even q.even,BivariatePolynomial.add p.odd q.odd⟩
def scale (a : ℚ) (p : Coefficients) : Coefficients :=
  ⟨BivariatePolynomial.scale a p.even,BivariatePolynomial.scale a p.odd⟩
def subtract (p q : Coefficients) : Coefficients := add p (scale (-1) q)

/-- The defining relation of the rotation circle, as a polynomial in c. -/
def relation : BivariatePolynomial.Coefficients := [[0,2,-1]]

def multiply (p q : Coefficients) : Coefficients :=
  ⟨BivariatePolynomial.add (BivariatePolynomial.multiply p.even q.even)
      (BivariatePolynomial.multiply relation (BivariatePolynomial.multiply p.odd q.odd)),
    BivariatePolynomial.add (BivariatePolynomial.multiply p.even q.odd) (BivariatePolynomial.multiply p.odd q.even)⟩

def derivative (p : Coefficients) : Coefficients :=
  ⟨BivariatePolynomial.derivative p.even,BivariatePolynomial.derivative p.odd⟩

def bound (p : Coefficients) (h a : ℚ) : ℚ :=
  BivariatePolynomial.bound p.even h (a^2/2)+a*BivariatePolynomial.bound p.odd h (a^2/2)

theorem value_add (p q : Coefficients) (t θ : ℝ) :
    value (add p q) t θ = value p t θ+value q t θ := by
  simp only [value,add,BivariatePolynomial.value_add]
  ring
theorem value_scale (a : ℚ) (p : Coefficients) (t θ : ℝ) :
    value (scale a p) t θ = (a:ℝ)*value p t θ := by
  simp only [value,scale,BivariatePolynomial.value_scale]
  ring
theorem value_subtract (p q : Coefficients) (t θ : ℝ) :
    value (subtract p q) t θ = value p t θ-value q t θ := by
  simp [subtract,value_add,value_scale,sub_eq_add_neg]

theorem relation_value (t θ : ℝ) :
    BivariatePolynomial.value relation t (1-Real.cos θ) = (Real.sin θ)^2 := by
  norm_num [relation,BivariatePolynomial.value,BivariatePolynomial.slice,
    BivariatePolynomial.row,Planning.PolynomialKernel.evaluate]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Multiplication is exact on the rotation circle at every real angle. -/
theorem value_multiply (p q : Coefficients) (t θ : ℝ) :
    value (multiply p q) t θ = value p t θ*value q t θ := by
  simp only [value,multiply,BivariatePolynomial.value_add,BivariatePolynomial.value_multiply,relation_value]
  ring

theorem value_derivative (p : Coefficients) (t θ : ℝ) :
    HasDerivAt (fun u => value p u θ) (value (derivative p) t θ) t := by
  exact (BivariatePolynomial.value_derivative p.even t (1-Real.cos θ)).add
    ((BivariatePolynomial.value_derivative p.odd t (1-Real.cos θ)).const_mul (Real.sin θ))

theorem cosine_bound (θ : ℝ) : |1-Real.cos θ| ≤ θ^2/2 := by
  have h := Real.abs_sin_le_abs (x := θ/2)
  have hc := Real.cos_two_mul (θ/2)
  have hh : 2*(θ/2) = θ := by ring
  rw [hh] at hc
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one θ))]
  nlinarith [Real.sin_sq_add_cos_sq (θ/2),sq_abs (Real.sin (θ/2)),sq_abs (θ/2),
    abs_nonneg (Real.sin (θ/2)),abs_nonneg (θ/2)]

theorem bound_sound (p : Coefficients) {h a : ℚ} {t θ : ℝ}
    (ht : |t| ≤ (h:ℝ)) (ha : |θ| ≤ (a:ℝ)) :
    |value p t θ| ≤ (bound p h a:ℝ) := by
  have hn : (0:ℝ) ≤ a := (abs_nonneg θ).trans ha
  have hc : |1-Real.cos θ| ≤ ((a^2/2:ℚ):ℝ) := by
    push_cast
    have hb := cosine_bound θ
    nlinarith [sq_abs θ,abs_nonneg θ]
  have he := BivariatePolynomial.bound_sound p.even ht hc
  have ho := BivariatePolynomial.bound_sound p.odd ht hc
  have hs := (Real.abs_sin_le_abs (x := θ)).trans ha
  have hm := mul_le_mul hs ho (abs_nonneg _) hn
  have hb := (abs_add_le (BivariatePolynomial.value p.even t (1-Real.cos θ))
    (Real.sin θ*BivariatePolynomial.value p.odd t (1-Real.cos θ))).trans
      (add_le_add he (by simpa only [abs_mul] using hm))
  simpa only [value,bound,Rat.cast_add,Rat.cast_mul] using hb

end GNC.CirclePolynomial
