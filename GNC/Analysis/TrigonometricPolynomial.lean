import GNC.Analysis.BivariatePolynomial
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Rational order-16 verification polynomials for sine and cosine, with
uniform Lagrange remainder bounds. The polynomial predictor may use these
to certify exact trigonometric forcing; the remainder is never discarded.
The Taylor theorem and trigonometric derivative bounds come from mathlib.
-/
noncomputable section
open Set Real GNC.BivariatePolynomial
namespace GNC.TrigonometricPolynomial

def sine : List ℚ :=
  [0,1,0,-1/6,0,1/120,0,-1/5040,0,1/362880,0,-1/39916800,0,
    1/6227020800,0,-1/1307674368000,0]
def cosine : List ℚ :=
  [1,0,-1/2,0,1/24,0,-1/720,0,1/40320,0,-1/3628800,0,
    1/479001600,0,-1/87178291200,0,1/20922789888000]

theorem taylor_set (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval f n (Icc 0 x) 0 x = taylorWithinEval f n univ 0 x := by
  rw [taylor_within_apply,taylor_within_apply]
  simp only [iteratedDerivWithin_univ]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
    (hf.of_le (show (k:WithTop ℕ∞) ≤ ⊤ from le_top)).contDiffAt (by simp [hx.le])]

theorem taylor_bound_pos (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) (n : ℕ)
    (hD : ∀ x, |iteratedDeriv (n+1) f x| ≤ 1) {x : ℝ} (hx : 0 < x) :
    |f x-taylorWithinEval f n univ 0 x| ≤ x^(n+1)/(n+1).factorial := by
  obtain ⟨y,_,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (n := n)
    hx (hf.of_le le_top).contDiffOn
  rw [taylor_set f hf n hx] at he
  rw [he,abs_div,abs_mul,abs_pow,sub_zero,abs_of_pos hx,Nat.abs_cast]
  exact div_le_div_of_nonneg_right
    (by simpa using mul_le_mul_of_nonneg_right (hD y) (pow_nonneg hx.le _))
    (by positivity)

theorem sine_taylor (x : ℝ) : taylorWithinEval sin 16 univ 0 x = row sine x := by
  norm_num [taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg,sine,row,Planning.PolynomialKernel.evaluate]
  ring
theorem cosine_taylor (x : ℝ) : taylorWithinEval cos 16 univ 0 x = row cosine x := by
  norm_num [taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg,cosine,row,Planning.PolynomialKernel.evaluate]
  ring

theorem sine_neg (x : ℝ) : row sine (-x) = -row sine x := by
  norm_num [sine,row,Planning.PolynomialKernel.evaluate]
theorem cosine_neg (x : ℝ) : row cosine (-x) = row cosine x := by
  norm_num [cosine,row,Planning.PolynomialKernel.evaluate]

theorem sine_bound_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |sin x-row sine x| ≤ x^17/355687428096000 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x
    norm_num [sine,row,Planning.PolynomialKernel.evaluate]
  · have h := taylor_bound_pos sin contDiff_sin 16 (abs_iteratedDeriv_sin_le_one 17) hp
    simpa only [sine_taylor] using h

theorem cosine_bound_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |cos x-row cosine x| ≤ x^17/355687428096000 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x
    norm_num [cosine,row,Planning.PolynomialKernel.evaluate]
  · have h := taylor_bound_pos cos contDiff_cos 16 (abs_iteratedDeriv_cos_le_one 17) hp
    simpa only [cosine_taylor] using h

theorem sine_bound (x : ℝ) : |sin x-row sine x| ≤ |x|^17/355687428096000 := by
  by_cases hx : 0 ≤ x
  · simpa only [abs_of_nonneg hx] using sine_bound_nonneg hx
  · have h := sine_bound_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    rw [sin_neg,sine_neg,show -sin x- -row sine x = -(sin x-row sine x) by ring,abs_neg] at h
    simpa only [abs_of_neg (lt_of_not_ge hx)] using h

theorem cosine_bound (x : ℝ) : |cos x-row cosine x| ≤ |x|^17/355687428096000 := by
  by_cases hx : 0 ≤ x
  · simpa only [abs_of_nonneg hx] using cosine_bound_nonneg hx
  · have h := cosine_bound_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    rw [cos_neg,cosine_neg] at h
    simpa only [abs_of_neg (lt_of_not_ge hx)] using h

end GNC.TrigonometricPolynomial
