import GNC.Analysis.TrigonometricPolynomial

/-! Degree-eight pointing-source bounds from released mathlib's Taylor
theorem. Source order is independent of the predictor's uncertainty order. -/
noncomputable section
namespace GNC.OcticPointing
open Real Set

def sine (θ : ℝ) : ℝ := θ-θ^3/6+θ^5/120-θ^7/5040
def cosineLoss (θ : ℝ) : ℝ := θ^2/2-θ^4/24+θ^6/720-θ^8/40320

private theorem sine_taylor (x : ℝ) : taylorWithinEval sin 8 univ 0 x=sine x := by
  norm_num [sine,taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg]
  ring
private theorem cosine_taylor (x : ℝ) : taylorWithinEval cos 9 univ 0 x=1-cosineLoss x := by
  norm_num [cosineLoss,taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_succ,
    Real.deriv_sin,deriv_cos',deriv.neg',deriv_neg]
  ring
private theorem sine_nonneg {x : ℝ} (hx : 0≤x) : |sin x-sine x|≤x^9/362880 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; norm_num [sine]
  · have h := TrigonometricPolynomial.taylor_bound_pos sin
      contDiff_sin 8 (abs_iteratedDeriv_sin_le_one 9) hp
    rw [sine_taylor] at h
    norm_num at h
    exact h
theorem sine_bound (x : ℝ) : |sin x-sine x|≤|x|^9/362880 := by
  by_cases hx : 0≤x
  · simpa [abs_of_nonneg hx] using sine_nonneg hx
  · have h := sine_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    have he : sin (-x)-sine (-x)=-(sin x-sine x) := by rw [sin_neg]; dsimp [sine]; ring
    rw [he,abs_neg] at h
    simpa [abs_of_neg (lt_of_not_ge hx)] using h
private theorem cosine_nonneg {x : ℝ} (hx : 0≤x) : |1-cos x-cosineLoss x|≤x^10/3628800 := by
  rcases eq_or_lt_of_le hx with he | hp
  · subst x; norm_num [cosineLoss]
  · have h := TrigonometricPolynomial.taylor_bound_pos cos contDiff_cos 9
      (abs_iteratedDeriv_cos_le_one 10) hp
    rw [cosine_taylor,show cos x-(1-cosineLoss x)=-(1-cos x-cosineLoss x) by ring,abs_neg] at h
    simpa using h
theorem cosine_bound (x : ℝ) : |1-cos x-cosineLoss x|≤|x|^10/3628800 := by
  by_cases hx : 0≤x
  · simpa [abs_of_nonneg hx] using cosine_nonneg hx
  · have h := cosine_nonneg (neg_nonneg.mpr (le_of_not_ge hx))
    simpa [cosineLoss,cos_neg,abs_of_neg (lt_of_not_ge hx),
      show (-x)^4=x^4 by ring,show (-x)^6=x^6 by ring,show (-x)^8=x^8 by ring] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem source_bound (θ : ℝ) (S C : E) :
    ‖(sin θ • S+(1-cos θ) • C)-(sine θ • S+cosineLoss θ • C)‖≤
      |θ|^9/362880*‖S‖+|θ|^10/3628800*‖C‖ := by
  have he : (sin θ • S+(1-cos θ) • C)-(sine θ • S+cosineLoss θ • C)=
      (sin θ-sine θ) • S+(1-cos θ-cosineLoss θ) • C := by module
  rw [he]
  exact (norm_add_le _ _).trans (by
    simp only [norm_smul,Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_right (sine_bound θ) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (cosine_bound θ) (norm_nonneg _)))

end GNC.OcticPointing
