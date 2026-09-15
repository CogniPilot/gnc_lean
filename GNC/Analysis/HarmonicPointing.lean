import GNC.Analysis.TrigonometricPolynomial
import GNC.Analysis.FiniteAngleComparison

/-! A small-amplitude pointing oscillation may have arbitrary phase. Expand
its amplitude while retaining the first two phase harmonics. The bound is
uniform in phase and hence in time and frequency; it is not a bound for an
arbitrary disturbance history with the same peak amplitude. -/
noncomputable section
set_option autoImplicit false
open Real Set
namespace GNC.HarmonicPointing

private theorem sine_taylor_two (x : ℝ) : taylorWithinEval sin 2 univ 0 x = x := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ, iteratedDeriv_succ,
    Real.deriv_sin, deriv_cos', deriv.neg', deriv_neg]

private theorem cosine_taylor_three (x : ℝ) :
    taylorWithinEval cos 3 univ 0 x = 1-x^2/2 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ, iteratedDeriv_succ,
    Real.deriv_sin, deriv_cos', deriv.neg', deriv_neg]
  ring

private theorem sine_linear_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |sin x-x| ≤ x^3/6 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; norm_num
  · simpa [sine_taylor_two] using TrigonometricPolynomial.taylor_bound_pos sin
      contDiff_sin 2 (abs_iteratedDeriv_sin_le_one 3) hp

theorem sine_linear_bound (x : ℝ) : |sin x-x| ≤ |x|^3/6 := by
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using sine_linear_nonneg hx
  · have h := sine_linear_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    rw [sin_neg, show -sin x- -x = -(sin x-x) by ring, abs_neg] at h
    simpa [abs_of_neg (lt_of_not_ge hx)] using h

private theorem cosine_quadratic_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |1-cos x-x^2/2| ≤ x^4/24 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; norm_num
  · have h := TrigonometricPolynomial.taylor_bound_pos cos contDiff_cos 3
      (abs_iteratedDeriv_cos_le_one 4) hp
    rw [cosine_taylor_three, show cos x-(1-x^2/2) = -(1-cos x-x^2/2) by ring,
      abs_neg] at h
    simpa using h

theorem cosine_quadratic_bound (x : ℝ) : |1-cos x-x^2/2| ≤ |x|^4/24 := by
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using cosine_quadratic_nonneg hx
  · have h := cosine_quadratic_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    simpa [cos_neg, abs_of_neg (lt_of_not_ge hx)] using h

theorem second_harmonic (amplitude phase : ℝ) :
    amplitude^2/4*(1-cos (2*phase)) = (amplitude*sin phase)^2/2 := by
  rw [cos_two_mul_eq_one_sub]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def source (amplitude phase : ℝ) (S C : E) : E :=
  (amplitude*sin phase) • S + (amplitude^2/4*(1-cos (2*phase))) • C

/-- `S = [k]× b` and `C = [k]×² b` give the Rodrigues thrust difference.
The source keeps full unknown phase, including the nonzero mean axial loss. -/
theorem source_bound (amplitude phase : ℝ) (ha : 0 ≤ amplitude) (S C : E) :
    ‖FiniteAngleComparison.exactAngle (amplitude*sin phase) S C -
      source amplitude phase S C‖ ≤ amplitude^3/6*‖S‖ + amplitude^4/24*‖C‖ := by
  have ht : |amplitude*sin phase| ≤ amplitude := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (abs_sin_le_one phase) ha).trans_eq (mul_one _)
  have hs : |sin (amplitude*sin phase)-amplitude*sin phase| ≤ amplitude^3/6 := by
    exact (sine_linear_bound _).trans (by gcongr)
  have hc : |1-cos (amplitude*sin phase)-(amplitude*sin phase)^2/2| ≤ amplitude^4/24 := by
    exact (cosine_quadratic_bound _).trans (by gcongr)
  have he : FiniteAngleComparison.exactAngle (amplitude*sin phase) S C -
      source amplitude phase S C =
      (sin (amplitude*sin phase)-amplitude*sin phase) • S +
      (1-cos (amplitude*sin phase)-(amplitude*sin phase)^2/2) • C := by
    simp only [FiniteAngleComparison.exactAngle, source, second_harmonic]
    module
  rw [he]
  calc
    _ ≤ ‖(sin (amplitude*sin phase)-amplitude*sin phase) • S‖ +
        ‖(1-cos (amplitude*sin phase)-(amplitude*sin phase)^2/2) • C‖ := norm_add_le _ _
    _ = |sin (amplitude*sin phase)-amplitude*sin phase| * ‖S‖ +
        |1-cos (amplitude*sin phase)-(amplitude*sin phase)^2/2| * ‖C‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end GNC.HarmonicPointing
