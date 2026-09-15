import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-! An explicit unit-forcing supersolution on normalized time `[0,1]`.
The denominator threshold is `8*7`, the second derivative coefficient of
the final monomial. No tolerance or fitted forcing margin is introduced. -/
noncomputable section
namespace GNC.PolynomialSupersolution
open Polynomial Set

def polynomial (κ : ℝ) : Polynomial ℝ :=
  C (1/2)*X^2+C (κ/24)*X^4+C (κ^2/720)*X^6+
    C (κ^3/(720*(56-κ)))*X^8

def value (κ t : ℝ) : ℝ := (polynomial κ).eval t
def velocity (κ t : ℝ) : ℝ := (polynomial κ).derivative.eval t
def acceleration (κ t : ℝ) : ℝ := (polynomial κ).derivative.derivative.eval t

theorem derivative (κ t : ℝ) : HasDerivAt (value κ) (velocity κ t) t :=
  (polynomial κ).hasDerivAt t

theorem velocity_derivative (κ t : ℝ) :
    HasDerivAt (velocity κ) (acceleration κ t) t :=
  (polynomial κ).derivative.hasDerivAt t

theorem initial (κ : ℝ) : value κ 0 = 0 ∧ velocity κ 0 = 0 := by
  simp [value,velocity,polynomial,derivative_add,derivative_mul,derivative_pow]

/-- The final coefficient closes the tail by a nonnegative polynomial,
rather than discarding it. -/
theorem defect_identity {κ : ℝ} (hκ : κ < 56) (t : ℝ) :
    acceleration κ t-κ*value κ t =
      1+κ^4/(720*(56-κ))*t^6*(1-t^2) := by
  have hd : (56:ℝ)-κ ≠ 0 := ne_of_gt (sub_pos.mpr hκ)
  simp [acceleration,value,polynomial,derivative_add,derivative_mul,derivative_pow]
  field_simp
  ring

theorem supersolution {κ t : ℝ} (hk : κ < 56)
    (ht : t ∈ Icc (0:ℝ) 1) : κ*value κ t+1 ≤ acceleration κ t := by
  have h := defect_identity hk t
  have ht2 : 0 ≤ 1-t^2 := sub_nonneg.mpr (pow_le_one₀ ht.1 ht.2)
  have hd : 0 < (56:ℝ)-κ := sub_pos.mpr hk
  have hn : 0 ≤ κ^4/(720*(56-κ))*t^6*(1-t^2) := by positivity
  linarith

theorem bounds {κ t : ℝ} (hκ : 0 ≤ κ) (hk : κ < 56)
    (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ value κ t ∧ value κ t ≤ value κ 1 ∧
      0 ≤ velocity κ t ∧ velocity κ t ≤ velocity κ 1 := by
  have hd : 0 < (56:ℝ)-κ := sub_pos.mpr hk
  have ht0 := ht.1
  simp only [value,velocity,polynomial,derivative_add,derivative_mul,derivative_C,
    derivative_pow,derivative_X,eval_add,eval_mul,eval_pow,eval_C,eval_X,
    zero_mul,zero_add,mul_one]
  constructor
  · positivity
  constructor
  · gcongr <;> first | exact ht.1 | exact ht.2
  constructor
  · positivity
  · gcongr <;> first | exact ht.1 | exact ht.2

end GNC.PolynomialSupersolution
