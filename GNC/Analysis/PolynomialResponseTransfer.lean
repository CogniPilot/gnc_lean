import GNC.Analysis.LinearResponsePolynomial

/-! Transfer a response certificate to different polynomial coefficients.
Every changed coefficient is charged uniformly over the time interval and
feature set. This covers unequal degrees, deleted entries and quantization.
-/
namespace GNC.PolynomialResponseTransfer
open LinearResponsePolynomial PolynomialBounds PolynomialOrder

def difference {n m : ℕ} (p q : Coefficients n m) : Coefficients n m :=
  fun i j => subtract (p i j) (q i j)

theorem response_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n m : ℕ} (basis : Fin n → E) (p q : Coefficients n m)
    (features : Fin m → ℝ) (s : ℝ) :
    response basis p features s-response basis q features s=
      response basis (difference p q) features s := by
  simp only [response, difference, value_subtract, sub_mul, sub_smul,
    Finset.sum_sub_distrib]

/-- Uniform transfer bound without assuming the modified predictor solves
the original response ODE. Its complete coefficient difference is bounded. -/
theorem difference_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n m : ℕ} (basis : Fin n → E) (hb : ∀ i, ‖basis i‖≤1)
    (p q : Coefficients n m) (features : Fin m → ℝ) (σ : Fin m → ℚ)
    (hf : ∀ j, |features j|≤(σ j:ℝ)) {h : ℚ} (hh : 0≤h) {s : ℝ}
    (hs : |s|≤(h:ℝ)) :
    ‖response basis p features s-response basis q features s‖≤
      (budget (difference p q) σ h:ℝ) := by
  rw [response_difference]
  simpa using response_bound basis hb (difference p q) features σ hf 0
    (by intro i j; simp [PolynomialTimeProfile.zeroPrefix]) hh hs
    (show (1:ℝ)∈Set.Icc 0 1 by constructor <;> norm_num)

end GNC.PolynomialResponseTransfer
