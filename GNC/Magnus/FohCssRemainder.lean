import GNC.Magnus.FohCssEquivalence
import GNC.Magnus.FohEndpointCertificate

/-! Two equal-interval integrated samples, corrected in logarithmic coordinates,
followed by the exact block exponential. This is an explicitly defined hybrid;
it is not an identification with every published physical-output CSS update.
The finite leading error and the complete actual-flow bound are separate facts.
-/
noncomputable section
namespace GNC.Magnus
open Set Finset

section Algebra
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The classical two-sample bracket weight applied to the full time-extended
generator increments, including the position/time block. -/
def twoSampleCorrectedExponent (a b : A) (T : ℝ) : A :=
  let d₁ := (T/2) • a + (T^2/8) • b
  let d₂ := (T/2) • a + (3*T^2/8) • b
  d₁ + d₂ + (2/3:ℝ) • comm d₁ d₂

theorem twoSampleCorrectedExponent_eq (a b : A) (T : ℝ) :
    twoSampleCorrectedExponent a b T =
      T • a + (T^2/2) • b + (T^3/12) • comm a b := by
  unfold twoSampleCorrectedExponent
  magnus_nc

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- The first potentially nonzero coefficient of exact flow minus corrected
exponential. This is a coefficient identity, not an infinite-tail estimate. -/
theorem corrected_exponential_fifth_error (a b : A) :
    flowCoeff a b 0 5 -
      expCoeff (Polynomial.monomial 1 a + Polynomial.monomial 2 ((1/2:ℝ) • b) +
        Polynomial.monomial 3 ((1/12:ℝ) • comm a b)) 5 =
      -(1/240:ℝ) • comm b (comm a b) -
        (1/720:ℝ) • comm a (comm a (comm a b)) := by
  norm_num [expCoeff, flowCoeff, pow_succ, Polynomial.coeff_mul,
    Polynomial.coeff_monomial, Polynomial.coeff_one,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  magnus_nc

end Algebra

section Analytic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

/-- Complete remainder bound for the corrected-sample ZOH exponential.
The finite polynomial difference preserves cancellation of low degrees.
The two remaining terms bound *all* omitted flow and exponential terms.
No Magnus convergence-radius assumption is needed. -/
theorem two_sample_corrected_flow_bound (a b : A) (Y : ℝ → A) (n m : ℕ)
    {T r : ℝ} (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t)
    (hr : ‖twoSampleCorrectedExponent a b T‖ ≤ r) (hm : r < m + 1) :
    ‖Y T - NormedSpace.exp (twoSampleCorrectedExponent a b T)‖ ≤
      AlgebraPolynomial.majorant (fohFiniteDifference a b n m) T +
      Real.exp ((‖a‖ + T * ‖b‖) * T) * (fohDefectRadius a b n T * T) +
      fohExpTail r m := by
  have hid : twoSampleCorrectedExponent a b T = fohRetainedExponent a b T :=
    twoSampleCorrectedExponent_eq a b T
  have h := foh_endpoint_certificate_geometric a b
    (twoSampleCorrectedExponent a b T) Y n m hT hY0 hY hr hm
  have hb := AlgebraPolynomial.norm_value_le (fohFiniteDifference a b n m)
    (show |T| ≤ T by rw [abs_of_nonneg hT])
  rw [fohFiniteDifference_value, ← hid] at hb
  exact h.trans (add_le_add (add_le_add hb le_rfl) le_rfl)

end Analytic
end GNC.Magnus
