import GNC.Magnus.FohFifthCertificate

/-! Midpoint higher-order Magnus polynomials for a right linear-input flow.
Finite coefficient statements and actual-ODE certificates are distinguished.
The midpoint is a+h*b/2, not a newly sampled input. -/
noncomputable section
namespace GNC.Magnus
open Polynomial Finset Set
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Midpoint generator as a polynomial in the interval length. -/
def fohMidpoint (a b : A) : Polynomial A := C a + monomial 1 ((1/2:ℝ) • b)

/-- Sixth-order candidate: odd midpoint Magnus terms through time degree five. -/
def fohMidpoint6 (a b : A) : Polynomial A :=
  let m := fohMidpoint a b
  let d := C b
  monomial 1 (1:A)*m + (1/12:ℝ) • (monomial 3 (1:A)*comm m d) -
  (1/240:ℝ) • (monomial 5 (1:A)*comm d (comm m d)) -
  (1/720:ℝ) • (monomial 5 (1:A)*comm m (comm m (comm m d)))

/-- Eighth-order candidate: also retain all midpoint time-degree-seven terms. -/
def fohMidpoint8 (a b : A) : Polynomial A :=
  let m := fohMidpoint a b
  let d := C b
  let c := comm m d
  fohMidpoint6 a b + monomial 7 (1:A) *
    ((1/30240:ℝ) • comm m (comm m (comm m (comm m c))) +
     (1/10080:ℝ) • comm m (comm m (comm d c)) -
     (1/7560:ℝ) • comm c (comm m c) +
     (1/6720:ℝ) • comm d (comm d c))

end GNC.Magnus

namespace GNC.Magnus
open Polynomial Finset Set
section Certificate
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def fohPolynomialDifference (a b : A) (p : Polynomial A) (n m : ℕ) : Polynomial A :=
  (∑ k ∈ range (n+1), Polynomial.monomial k (flowCoeff a b 0 k)) -
  ∑ j ∈ range m, ((Nat.factorial j:ℝ)⁻¹) • p^j

omit [CompleteSpace A] in
theorem fohPolynomialDifference_value (a b : A) (p : Polynomial A) (n m : ℕ) (t : ℝ) :
    AlgebraPolynomial.value (fohPolynomialDifference a b p n m) t =
      fohTaylor a b n t - ExponentialCertificate.polynomial (AlgebraPolynomial.value p t) m := by
  simp only [fohPolynomialDifference, AlgebraPolynomial.value_sub, AlgebraPolynomial.value_sum,
    AlgebraPolynomial.value_monomial, AlgebraPolynomial.value_smul, AlgebraPolynomial.value_pow,
    fohTaylor, ExponentialCertificate.polynomial]

/-- Actual-ODE error certificate for any polynomial exponent, including both midpoint methods.
This theorem does not assume an order statement or a Magnus-tail bound. -/
theorem foh_polynomial_defect_certificate [NormOneClass A]
    (a b : A) (p : Polynomial A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t*(a+t • b)) t)
    (hr : ‖AlgebraPolynomial.value p T‖ ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) :
    ‖Y T-NormedSpace.exp (AlgebraPolynomial.value p T)‖ ≤
      AlgebraPolynomial.majorant (fohPolynomialDifference a b p n m) T +
      Real.exp ((‖a‖+T*‖b‖)*T) * (fohDefectRadius a b n T*T) +
      r^m*(m+1)/(Nat.factorial m*m) := by
  have hf := fohTaylor_error_bound a b Y n hT hY0 hY
  have he := ExponentialCertificate.remainder_bound (AlgebraPolynomial.value p T) hr hr1 m hm
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (Y T) (fohTaylor a b n T) (NormedSpace.exp (AlgebraPolynomial.value p T))
  have hp := norm_sub_le_norm_sub_add_norm_sub
    (fohTaylor a b n T)
    (ExponentialCertificate.polynomial (AlgebraPolynomial.value p T) m)
    (NormedSpace.exp (AlgebraPolynomial.value p T))
  rw [norm_sub_rev (ExponentialCertificate.polynomial _ _)] at hp
  have hb := AlgebraPolynomial.norm_value_le (fohPolynomialDifference a b p n m)
    (show |T| ≤ T by rw [abs_of_nonneg hT])
  rw [fohPolynomialDifference_value] at hb
  linarith
end Certificate
end GNC.Magnus
