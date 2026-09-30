import GNC.Magnus.FohDefectCertificate

/-! The degree-five corrected one-exponential linear-input step. The existing
Magnus jet identifies its coefficients; these results attach a complete
actual-ODE certificate and prove the additional finite cancellation. -/
noncomputable section
namespace GNC.Magnus
open Set Finset
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def fohFifthExponent (a b : A) (t : ℝ) : A :=
  AlgebraPolynomial.value (exponent5 a b 0) t

def fohFifthDifference (a b : A) (n m : ℕ) : Polynomial A :=
  (∑ k ∈ range (n+1), Polynomial.monomial k (flowCoeff a b 0 k)) -
  ∑ j ∈ range m, ((Nat.factorial j:ℝ)⁻¹) • (exponent5 a b 0)^j

omit [CompleteSpace A] in
theorem fohFifthDifference_value (a b : A) (n m : ℕ) (t : ℝ) :
    AlgebraPolynomial.value (fohFifthDifference a b n m) t =
      fohTaylor a b n t - ExponentialCertificate.polynomial (fohFifthExponent a b t) m := by
  simp only [fohFifthDifference, AlgebraPolynomial.value_sub, AlgebraPolynomial.value_sum,
    AlgebraPolynomial.value_monomial, AlgebraPolynomial.value_smul, AlgebraPolynomial.value_pow,
    fohFifthExponent, fohTaylor, ExponentialCertificate.polynomial]

omit [CompleteSpace A] in
/-- The corrected exponent matches the flow through degree five. -/
theorem fohFifthDifference_low_coeff (a b : A) (n m k : ℕ)
    (hn : 5 ≤ n) (hm : 6 ≤ m) (hk : k ≤ 5) :
    (fohFifthDifference a b n m).coeff k = 0 := by
  rw [fohFifthDifference, Polynomial.coeff_sub,
    foh_truncated_exp_coeff _ (exponent5_constant a b 0) m k (by omega),
    exponent5_flow_coeff a b 0 k hk]
  have hkn : k < n+1 := by omega
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hkn]

/-- Full-flow certificate, not merely a formal coefficient statement. -/
theorem foh_fifth_defect_certificate [NormOneClass A]
    (a b : A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t*(a+t • b)) t)
    (hr : ‖fohFifthExponent a b T‖ ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) :
    ‖Y T-NormedSpace.exp (fohFifthExponent a b T)‖ ≤
      AlgebraPolynomial.majorant (fohFifthDifference a b n m) T +
      Real.exp ((‖a‖+T*‖b‖)*T) * (fohDefectRadius a b n T*T) +
      r^m*(m+1)/(Nat.factorial m*m) := by
  have hf := fohTaylor_error_bound a b Y n hT hY0 hY
  have he := ExponentialCertificate.remainder_bound (fohFifthExponent a b T) hr hr1 m hm
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (Y T) (fohTaylor a b n T) (NormedSpace.exp (fohFifthExponent a b T))
  have hp := norm_sub_le_norm_sub_add_norm_sub
    (fohTaylor a b n T)
    (ExponentialCertificate.polynomial (fohFifthExponent a b T) m)
    (NormedSpace.exp (fohFifthExponent a b T))
  rw [norm_sub_rev (ExponentialCertificate.polynomial _ _)] at hp
  have hb := AlgebraPolynomial.norm_value_le (fohFifthDifference a b n m)
    (show |T| ≤ T by rw [abs_of_nonneg hT])
  rw [fohFifthDifference_value] at hb
  linarith

end GNC.Magnus
