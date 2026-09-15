import GNC.Analysis.SmallAngle
import GNC.Analysis.TrigonometricPolynomial

/-!
An independent check of the degree-four trigonometric formulas observed in
the pinned external Taylor-model implementation. Dividing a raw power by
its degree instead of its factorial creates an error of lower order than
the advertised Taylor remainder. These are mathematical counterexamples;
they do not formalize the C++ execution or assert soundness of its repair.
-/
noncomputable section
namespace GNC.OrbitalComparison.ExternalTaylorReview
open Real

def degreeDividedSine (x : ℝ) : ℝ := x-x^3/3
def degreeDividedCosine (x : ℝ) : ℝ := 1-x^2/2+x^4/4

theorem sine_taylor_four (x : ℝ) :
    taylorWithinEval sin 4 Set.univ 0 x = x-x^3/6 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ,
    iteratedDeriv_succ, Real.deriv_sin, deriv_cos', deriv.neg', deriv_neg]
  ring

theorem sine_coefficient_defect (x : ℝ) :
    (x-x^3/6)-degreeDividedSine x = x^3/6 := by
  unfold degreeDividedSine
  ring

theorem cosine_coefficient_defect (x : ℝ) :
    degreeDividedCosine x-(1-x^2/2+x^4/24) = 5*x^4/24 := by
  unfold degreeDividedCosine
  ring

/-- The mismatch is already cubic; the fifth-order Taylor tail cannot
repair it merely by increasing the precision of arithmetic. -/
theorem sine_error_lower {x : ℝ} (hx : 0 < x) :
    x^3/6-x^5/120 ≤ sin x-degreeDividedSine x := by
  have h := TrigonometricPolynomial.taylor_bound_pos sin contDiff_sin 4
    (abs_iteratedDeriv_sin_le_one 5) hx
  rw [sine_taylor_four] at h
  norm_num [Nat.factorial] at h
  have hlow := (abs_le.mp h).1
  dsimp [degreeDividedSine]
  linarith

theorem cosine_error_lower {x : ℝ} (hx : 0 < x) :
    5*x^4/24-x^5/120 ≤ degreeDividedCosine x-cos x := by
  have h := TrigonometricPolynomial.taylor_bound_pos cos contDiff_cos 4
    (abs_iteratedDeriv_cos_le_one 5) hx
  rw [Coefficients.cos_taylor_four] at h
  norm_num [Nat.factorial] at h
  have hupp := (abs_le.mp h).2
  dsimp [degreeDividedCosine]
  linarith

/-- At x = 1/2, even the full fifth-order Lagrange radius is insufficient
when attached to the wrong sine polynomial. -/
theorem sine_half_excludes_with_lagrange_radius :
    degreeDividedSine (1/2)+1/3840 < sin (1/2) := by
  have h := sine_error_lower (x := (1:ℝ)/2) (by norm_num)
  norm_num [degreeDividedSine] at h ⊢
  linarith

theorem cosine_half_excludes_with_lagrange_radius :
    cos (1/2) < degreeDividedCosine (1/2)-1/3840 := by
  have h := cosine_error_lower (x := (1:ℝ)/2) (by norm_num)
  norm_num [degreeDividedCosine] at h ⊢
  linarith

end GNC.OrbitalComparison.ExternalTaylorReview
