import GNC.Analysis.MonomialProfile

/-! Exact rational endpoint evaluation of the polynomial envelopes.
This permits kernel-checked mission data without trusting a floating evaluator. -/
namespace GNC.MonomialRational

def pair (n : ℕ) : ℚ := ((n:ℚ)+1)*((n:ℚ)+2)
def endpoint (κ : ℚ) (n : ℕ) : ℚ :=
  1/pair n + κ/(pair n*pair (n+2)) + κ^2/(pair n*pair (n+2)*pair (n+4)) +
  κ^3/(pair n*pair (n+2)*pair (n+4)*(pair (n+6)-κ))

theorem cast_endpoint (κ : ℚ) (n : ℕ) :
    (endpoint κ n:ℝ)=MonomialSupersolution.value (κ:ℝ) n 1 := by
  simp [endpoint, pair, MonomialSupersolution.value, MonomialSupersolution.polynomial,
    MonomialSupersolution.pair, MonomialSupersolution.four, MonomialSupersolution.six]

theorem cast_constant (κ : ℚ) :
    (endpoint κ 0:ℝ)=PolynomialSupersolution.value (κ:ℝ) 1 := by
  norm_num [endpoint, pair, PolynomialSupersolution.value, PolynomialSupersolution.polynomial]

end GNC.MonomialRational
