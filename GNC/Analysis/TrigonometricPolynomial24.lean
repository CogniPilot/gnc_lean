import GNC.Analysis.TrigonometricPolynomial

/-! Degree-24 source polynomials. The Taylor and derivative-bound theorems
are reused from released mathlib; only the concrete coefficient identities
and their specialization are checked here. -/
noncomputable section
open Set Real GNC.BivariatePolynomial
namespace GNC.TrigonometricPolynomial24

def sine : List ℚ :=
  [0,1,0,-1/6,0,1/120,0,-1/5040,0,1/362880,0,-1/39916800,0,1/6227020800,0,-1/1307674368000,0,1/355687428096000,0,-1/121645100408832000,0,1/51090942171709440000,0,-1/25852016738884976640000,0]
def cosine : List ℚ :=
  [1,0,-1/2,0,1/24,0,-1/720,0,1/40320,0,-1/3628800,0,1/479001600,0,-1/87178291200,0,1/20922789888000,0,-1/6402373705728000,0,1/2432902008176640000,0,-1/1124000727777607680000,0,1/620448401733239439360000]

theorem sine_taylor (x : ℝ) : taylorWithinEval sin 24 univ 0 x = row sine x := by
  norm_num [taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg,sine,row,Planning.PolynomialKernel.evaluate]
  ring
theorem cosine_taylor (x : ℝ) : taylorWithinEval cos 24 univ 0 x = row cosine x := by
  norm_num [taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg,cosine,row,Planning.PolynomialKernel.evaluate]
  ring

theorem sine_neg (x : ℝ) : row sine (-x) = -row sine x := by
  norm_num [sine,row,Planning.PolynomialKernel.evaluate]
theorem cosine_neg (x : ℝ) : row cosine (-x) = row cosine x := by
  norm_num [cosine,row,Planning.PolynomialKernel.evaluate]

theorem sine_bound_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |sin x-row sine x| ≤ x^25/15511210043330985984000000 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x
    norm_num [sine,row,Planning.PolynomialKernel.evaluate]
  · have h := TrigonometricPolynomial.taylor_bound_pos sin contDiff_sin 24 (abs_iteratedDeriv_sin_le_one 25) hp
    simpa only [sine_taylor] using h

theorem cosine_bound_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |cos x-row cosine x| ≤ x^25/15511210043330985984000000 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x
    norm_num [cosine,row,Planning.PolynomialKernel.evaluate]
  · have h := TrigonometricPolynomial.taylor_bound_pos cos contDiff_cos 24 (abs_iteratedDeriv_cos_le_one 25) hp
    simpa only [cosine_taylor] using h

theorem sine_bound (x : ℝ) : |sin x-row sine x| ≤ |x|^25/15511210043330985984000000 := by
  by_cases hx : 0 ≤ x
  · simpa only [abs_of_nonneg hx] using sine_bound_nonneg hx
  · have h := sine_bound_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    rw [sin_neg,sine_neg,show -sin x- -row sine x = -(sin x-row sine x) by ring,abs_neg] at h
    simpa only [abs_of_neg (lt_of_not_ge hx)] using h

theorem cosine_bound (x : ℝ) : |cos x-row cosine x| ≤ |x|^25/15511210043330985984000000 := by
  by_cases hx : 0 ≤ x
  · simpa only [abs_of_nonneg hx] using cosine_bound_nonneg hx
  · have h := cosine_bound_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    rw [cos_neg,cosine_neg] at h
    simpa only [abs_of_neg (lt_of_not_ge hx)] using h

end GNC.TrigonometricPolynomial24
