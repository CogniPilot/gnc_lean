import GNC.Magnus.FohCssRemainder

/-! The residual of the two-sample corrected-log/ZOH exponential, with
its first two nonzero time coefficients separated from a complete tail.
This does not identify a separately truncated physical-output CSS update
with the group exponential. -/
noncomputable section
namespace GNC.Magnus
open Set Finset

section Algebra
variable {A : Type*} [Ring A] [Algebra ℝ A]

def cssErrorFive (a b : A) : A :=
  -(1/240:ℝ) • comm b (comm a b) -
    (1/720:ℝ) • comm a (comm a (comm a b))

def cssErrorSix (a b : A) : A :=
  (1/2:ℝ) • (a * cssErrorFive a b + cssErrorFive a b * a) -
    (1/720:ℝ) • comm a (comm b (comm a b))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 12000000 in
/-- The sixth time coefficient includes propagation of the fifth error;
it is not just the next Magnus commutator. -/
theorem corrected_exponential_sixth_error (a b : A) :
    flowCoeff a b 0 6 - expCoeff
      (Polynomial.monomial 1 a + Polynomial.monomial 2 ((1/2:ℝ) • b) +
        Polynomial.monomial 3 ((1/12:ℝ) • comm a b)) 6 =
      cssErrorSix a b := by
  norm_num [expCoeff, flowCoeff, pow_succ,
    Polynomial.coeff_mul, Polynomial.coeff_monomial, Polynomial.coeff_one,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  unfold cssErrorSix cssErrorFive
  magnus_nc

end Algebra

open Matrix in
/-- Rotation acts on translation while the time corner transfers velocity
to position. Keeping the columns separate avoids large entry expansions. -/
theorem css_rotation_translation_bracket (w a p v : Vec3) :
    comm (extended ![0,a,w] 1) (extended ![p,v,0] 0) =
      extended ![crossProduct w p - v, crossProduct w v, 0] 0 := by
  rw [comm, extended_commutator]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extendedBracket, ad, crossProduct, vecHead, vecTail] <;> ring

set_option maxHeartbeats 2000000 in
open Matrix in
/-- Even with constant gyro, affine acceleration generally leaves a
translation residual in the corrected-log/ZOH update. Mean-removed FOH
preintegration, by contrast, retains these translation integrals exactly. -/
theorem cssErrorFive_constant_gyro (w a b : Vec3) :
    cssErrorFive (extended ![0,a,w] 1) (extended ![0,b,0] 0) =
      extended ![(1/240:ℝ) • crossProduct w (crossProduct w b),
        -(1/720:ℝ) • crossProduct w (crossProduct w (crossProduct w b)), 0] 0 := by
  have hc : comm (extended ![0,a,w] 1) (extended ![0,b,0] 0) =
      extended ![-b, crossProduct w b, 0] 0 := by
    simpa [comm, crossProduct] using foh_commutator w a 0 b
  have hz : comm (extended ![0,b,0] 0)
      (extended ![-b,crossProduct w b,0] 0) = 0 := by
    rw [comm, extended_commutator]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [extendedBracket, ad, extended, hat, crossProduct]
  unfold cssErrorFive
  rw [hc, hz, css_rotation_translation_bracket, css_rotation_translation_bracket]
  simp only [smul_zero, zero_sub, ← neg_smul]
  rw [← extended_smul]
  simp only [mul_zero]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossProduct, vecHead, vecTail] <;> ring

section Analytic
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Finite truncations retain any coefficient below both cutoffs. -/
theorem fohFiniteDifference_coeff (a b : A) (n m k : ℕ)
    (hn : k ≤ n) (hm : k < m) :
    (fohFiniteDifference a b n m).coeff k =
      flowCoeff a b 0 k - expCoeff (fohExponentPolynomial a b) k := by
  have hp : (fohExponentPolynomial a b).coeff 0 = 0 := by
    simp [fohExponentPolynomial, Polynomial.coeff_monomial]
  rw [fohFiniteDifference, Polynomial.coeff_sub, foh_truncated_exp_coeff _ hp m k hm]
  have hkn : k < n+1 := by omega
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hkn]

/-- A finite witness for the remainder *after* removing the exact fifth
and sixth coefficients. -/
def cssHigherDifference (a b : A) (n m : ℕ) : Polynomial A :=
  fohFiniteDifference a b n m -
    (Polynomial.monomial 5 (cssErrorFive a b) +
      Polynomial.monomial 6 (cssErrorSix a b))

omit [CompleteSpace A] in
theorem cssHigherDifference_low_coeff (a b : A) (n m k : ℕ)
    (hn : 6 ≤ n) (hm : 7 ≤ m) (hk : k ≤ 6) :
    (cssHigherDifference a b n m).coeff k = 0 := by
  by_cases h4 : k ≤ 4
  · simp only [cssHigherDifference, Polynomial.coeff_sub, Polynomial.coeff_add]
    rw [fohFiniteDifference_low_coeff a b n m k (by omega) (by omega) h4]
    simp [Polynomial.coeff_monomial, show 5 ≠ k by omega, show 6 ≠ k by omega]
  · have hcases : k = 5 ∨ k = 6 := by omega
    rcases hcases with rfl | rfl
    · rw [cssHigherDifference, Polynomial.coeff_sub, Polynomial.coeff_add,
        fohFiniteDifference_coeff a b n m 5 (by omega) (by omega)]
      have h := corrected_exponential_fifth_error a b
      change flowCoeff a b 0 5 - expCoeff (fohExponentPolynomial a b) 5 =
        cssErrorFive a b at h
      simp [h, Polynomial.coeff_monomial]
    · rw [cssHigherDifference, Polynomial.coeff_sub, Polynomial.coeff_add,
        fohFiniteDifference_coeff a b n m 6 hn (by omega)]
      have h := corrected_exponential_sixth_error a b
      change flowCoeff a b 0 6 - expCoeff (fohExponentPolynomial a b) 6 =
        cssErrorSix a b at h
      simp [h, Polynomial.coeff_monomial]

/-- A complete bound on the actual residual after removing its first two
coefficients. The finite witness cancels through time degree six; both
infinite tails are included, and no Magnus convergence assumption is made. -/
theorem corrected_exponential_higher_remainder [NormOneClass A]
    (a b : A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t)
    (hr : ‖fohRetainedExponent a b T‖ ≤ r) (hm : r < m + 1) :
    ‖(Y T - NormedSpace.exp (fohRetainedExponent a b T)) -
      (T^5 • cssErrorFive a b + T^6 • cssErrorSix a b)‖ ≤
      ‖AlgebraPolynomial.value (cssHigherDifference a b n m) T‖ +
      Real.exp ((‖a‖ + T * ‖b‖) * T) * (fohDefectRadius a b n T * T) +
      fohExpTail r m := by
  let Q := fohTaylor a b n T
  let S := ExponentialCertificate.polynomial (fohRetainedExponent a b T) m
  let L := T^5 • cssErrorFive a b + T^6 • cssErrorSix a b
  have hf := fohTaylor_error_bound a b Y n hT hY0 hY
  have he := foh_exp_tail (fohRetainedExponent a b T) hr m hm
  have hv : AlgebraPolynomial.value (cssHigherDifference a b n m) T = Q - S - L := by
    simp only [cssHigherDifference, AlgebraPolynomial.value_sub,
      AlgebraPolynomial.value_add, AlgebraPolynomial.value_monomial,
      fohFiniteDifference_value, Q, S, L]
  have hid : (Y T - NormedSpace.exp (fohRetainedExponent a b T)) - L =
      (Y T - Q) + (Q - S - L) + (S - NormedSpace.exp (fohRetainedExponent a b T)) := by
    abel
  rw [hid]
  rw [hv]
  have ht : ‖(Y T - Q) + (Q - S - L) +
      (S - NormedSpace.exp (fohRetainedExponent a b T))‖ ≤
      ‖Y T - Q‖ + ‖Q - S - L‖ +
        ‖S - NormedSpace.exp (fohRetainedExponent a b T)‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_sub_rev S] at ht
  exact ht.trans (by
    simpa [Q, S, add_comm, add_left_comm, add_assoc] using
      add_le_add (add_le_add hf (le_refl ‖Q - S - L‖)) he)

/-- Stable coefficientwise alternative, with exact cancellation through
degree six when the cutoffs are at least six and seven. -/
theorem corrected_exponential_higher_coefficient_remainder [NormOneClass A]
    (a b : A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t * (a + t • b)) t)
    (hr : ‖fohRetainedExponent a b T‖ ≤ r) (hm : r < m + 1) :
    ‖(Y T - NormedSpace.exp (fohRetainedExponent a b T)) -
      (T^5 • cssErrorFive a b + T^6 • cssErrorSix a b)‖ ≤
      AlgebraPolynomial.majorant (cssHigherDifference a b n m) T +
      Real.exp ((‖a‖ + T * ‖b‖) * T) * (fohDefectRadius a b n T * T) +
      fohExpTail r m := by
  apply (corrected_exponential_higher_remainder a b Y n m hT hY0 hY hr hm).trans
  exact add_le_add (add_le_add (AlgebraPolynomial.norm_value_le _
    (show |T| ≤ T by rw [abs_of_nonneg hT])) le_rfl) le_rfl

end Analytic
end GNC.Magnus
