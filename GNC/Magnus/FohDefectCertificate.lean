import GNC.Magnus.MagnusJet
import GNC.Analysis.ArcGronwall
import GNC.Analysis.ExponentialCertificate
import GNC.Analysis.AlgebraPolynomial

/-! Complete FOH flow certificates from a finite polynomial's actual ODE
 defect. No identification of an infinite formal series with the ODE solution
 is required. The exponential tail is the existing analytic exponential
 remainder theorem, not an assumed Magnus remainder. -/
noncomputable section
namespace GNC.Magnus
open Set Finset
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Finite Taylor polynomial of the right linear-input flow. -/
def fohTaylor (a b : A) (n : ℕ) (t : ℝ) : A :=
  ∑ k ∈ range (n+1), t^k • flowCoeff a b 0 k

omit [CompleteSpace A] in
/-- The recurrence fixes each derivative coefficient without any analytic
 series identification. -/
theorem foh_coeff_step (a b : A) (n : ℕ) :
    ((n+2:ℕ):ℝ) • flowCoeff a b 0 (n+2) =
      flowCoeff a b 0 (n+1)*a + flowCoeff a b 0 n*b := by
  rw [show n+2 = (n+1)+1 by omega, flowCoeff]
  simp only [mul_zero, add_zero, show ¬ n+1=0 by omega, if_false,
    Nat.add_sub_cancel, smul_smul, ite_self, add_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_inv_cancel₀ (by positivity : (↑n+1+1:ℝ) ≠ 0), one_smul]

omit [CompleteSpace A] in
theorem foh_coeff_one (a b : A) : flowCoeff a b 0 1 = a := by
  simp [flowCoeff]

omit [CompleteSpace A] in
/-- Exact defect of the finite polynomial, valid in a noncommutative algebra. -/
theorem fohTaylor_derivative (a b : A) (n : ℕ) (t : ℝ) :
    HasDerivAt (fohTaylor a b n)
      (fohTaylor a b n t * (a+t • b) -
       t^n • (((n+1:ℕ):ℝ) • flowCoeff a b 0 (n+1)) -
       t^(n+1) • (flowCoeff a b 0 n*b)) t := by
  induction n with
  | zero =>
    convert hasDerivAt_const t (1:A) using 1
    · funext u; simp [fohTaylor, flowCoeff]
    · simp [fohTaylor, flowCoeff]
  | succ n ih =>
    have hpow := ((hasDerivAt_id t).pow (n+1)).smul_const (flowCoeff a b 0 (n+1))
    have hd := ih.add hpow
    have hfun : fohTaylor a b (n+1) = fun t =>
        fohTaylor a b n t + t^(n+1) • flowCoeff a b 0 (n+1) := by
      funext t
      simp only [fohTaylor, sum_range_succ]
    rw [hfun]
    convert hd using 1
    rw [foh_coeff_step]
    simp only [id_eq, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
      mul_one, pow_succ, smul_smul, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_add]
    module

omit [CompleteSpace A] in
theorem fohTaylor_initial (a b : A) (n : ℕ) : fohTaylor a b n 0 = 1 := by
  rw [fohTaylor, sum_range_succ']
  simp [flowCoeff]

/-- Uniform norm envelope of the exactly computed polynomial defect. -/
def fohDefectRadius (a b : A) (n : ℕ) (T : ℝ) : ℝ :=
  T^n * ‖((n+1:ℕ):ℝ) • flowCoeff a b 0 (n+1)‖ +
  T^(n+1) * ‖flowCoeff a b 0 n*b‖

omit [CompleteSpace A] in
theorem fohDefectRadius_nonneg (a b : A) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ fohDefectRadius a b n T := by
  unfold fohDefectRadius
  positivity

/-- The actual right-flow ODE is compared to a finite polynomial. No analytic
series equality or tail bound is supplied as a hypothesis. -/
theorem fohTaylor_error_bound (a b : A) (Y : ℝ → A) (n : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t*(a+t • b)) t) :
    ‖Y T-fohTaylor a b n T‖ ≤
      Real.exp ((‖a‖+T*‖b‖)*T) * (fohDefectRadius a b n T*T) := by
  let q := fohTaylor a b n
  let e := fun t => Y t-q t
  let de := fun t => e t*(a+t • b) +
    t^n • (((n+1:ℕ):ℝ) • flowCoeff a b 0 (n+1)) +
    t^(n+1) • (flowCoeff a b 0 n*b)
  let K := ‖a‖+T*‖b‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hqc : Continuous q := continuous_iff_continuousAt.mpr
    (fun t => (fohTaylor_derivative a b n t).continuousAt)
  have hYc : ContinuousOn Y (Icc 0 T) := fun t ht =>
    (hY t ht).continuousAt.continuousWithinAt
  have hec : ContinuousOn e (Icc 0 T) := hYc.sub hqc.continuousOn
  have hdec : ContinuousOn de (Icc 0 T) :=
    ((hec.mul (continuousOn_const.add (continuousOn_id.smul continuousOn_const))).add
      ((continuousOn_id.pow n).smul continuousOn_const)).add
        ((continuousOn_id.pow (n+1)).smul continuousOn_const)
  have hed (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt e (de t) t := by
    convert (hY t ⟨ht.1.le,ht.2.le⟩).sub (fohTaylor_derivative a b n t) using 1
    dsimp [e, de, q]
    rw [sub_mul]
    abel
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) : ‖de t‖ ≤ K*‖e t‖+fohDefectRadius a b n T := by
    have hN : ‖a+t • b‖ ≤ K := by
      calc ‖a+t • b‖ ≤ ‖a‖+‖t • b‖ := norm_add_le _ _
        _ = ‖a‖+t*‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        _ ≤ K := add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _))
    have hp (k : ℕ) (v : A) : ‖t^k • v‖ ≤ T^k*‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1 _)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.1 ht.2.le _) (norm_nonneg _)
    calc ‖de t‖ ≤ (‖e t*(a+t • b)‖+
        ‖t^n • (((n+1:ℕ):ℝ) • flowCoeff a b 0 (n+1))‖) +
        ‖t^(n+1) • (flowCoeff a b 0 n*b)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (‖e t‖*K+T^n*‖((n+1:ℕ):ℝ) • flowCoeff a b 0 (n+1)‖)+
        T^(n+1)*‖flowCoeff a b 0 n*b‖ := by
          exact add_le_add (add_le_add ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left hN (norm_nonneg _))) (hp n _)) (hp (n+1) _)
      _ = K*‖e t‖+fohDefectRadius a b n T := by unfold fohDefectRadius; ring
  have hi : ‖e 0‖ ≤ Real.exp (K*0)*0 := by
    simp [e, q, hY0, fohTaylor_initial]
  have hg := ArcGronwall.growth e de (a := 0) (b := T) (by norm_num) hK
    (fohDefectRadius_nonneg a b n hT) hec hdec hed hb hi T ⟨hT, le_rfl⟩
  simpa [e, q, K] using hg

/-- Retained one-commutator exponent of the FOH step. -/
def fohRetainedExponent (a b : A) (T : ℝ) : A :=
  T • a + (T^2/2) • b + (T^3/12) • comm a b

omit [CompleteSpace A] in
/-- An explicitly computable radius for the retained exponent. -/
theorem fohRetainedExponent_norm (a b : A) {T : ℝ} (hT : 0 ≤ T) :
    ‖fohRetainedExponent a b T‖ ≤
      T*‖a‖ + T^2/2*‖b‖ + T^3/12*‖comm a b‖ := by
  unfold fohRetainedExponent
  calc ‖T • a + (T^2/2) • b + (T^3/12) • comm a b‖ ≤
      (‖T • a‖+‖(T^2/2) • b‖)+‖(T^3/12) • comm a b‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hT, abs_of_nonneg (by positivity : 0 ≤ T^2/2),
        abs_of_nonneg (by positivity : 0 ≤ T^3/12)]

/-- A complete computable flow-error certificate. The norm of the difference
of the TWO FINITE polynomials is evaluated before any triangle bound. The
only analytic tails are proved from the actual ODE defect and the convergent
exponential series. `m` counts retained exponential powers, from 0 to m-1. -/
theorem foh_defect_certificate [NormOneClass A]
    (a b : A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t*(a+t • b)) t)
    (hr : ‖fohRetainedExponent a b T‖ ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) :
    ‖Y T-NormedSpace.exp (fohRetainedExponent a b T)‖ ≤
      ‖fohTaylor a b n T -
        ExponentialCertificate.polynomial (fohRetainedExponent a b T) m‖ +
      Real.exp ((‖a‖+T*‖b‖)*T) * (fohDefectRadius a b n T*T) +
      r^m*(m+1)/(Nat.factorial m*m) := by
  have hf := fohTaylor_error_bound a b Y n hT hY0 hY
  have he := ExponentialCertificate.remainder_bound (fohRetainedExponent a b T) hr hr1 m hm
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (Y T) (fohTaylor a b n T) (NormedSpace.exp (fohRetainedExponent a b T))
  have hfinite := norm_sub_le_norm_sub_add_norm_sub
    (fohTaylor a b n T)
    (ExponentialCertificate.polynomial (fohRetainedExponent a b T) m)
    (NormedSpace.exp (fohRetainedExponent a b T))
  rw [norm_sub_rev (ExponentialCertificate.polynomial _ _)] at hfinite
  linarith

/-- Entirely finite real-arithmetic form on a short interval. Even the
Gronwall factor is bounded by a finite scalar exponential polynomial plus
its proved rational remainder. -/
theorem foh_defect_certificate_finite [NormOneClass A]
    (a b : A) (Y : ℝ → A) (n m l : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t*(a+t • b)) t)
    (hr : ‖fohRetainedExponent a b T‖ ≤ r) (hr1 : r ≤ 1) (hm : 0 < m)
    (hshort : (‖a‖+T*‖b‖)*T ≤ 1) (hl : 0 < l) :
    ‖Y T-NormedSpace.exp (fohRetainedExponent a b T)‖ ≤
      ‖fohTaylor a b n T -
        ExponentialCertificate.polynomial (fohRetainedExponent a b T) m‖ +
      (ExponentialCertificate.scalarPolynomial ((‖a‖+T*‖b‖)*T) l +
        ((‖a‖+T*‖b‖)*T)^l*(l+1)/(Nat.factorial l*l)) *
          (fohDefectRadius a b n T*T) +
      r^m*(m+1)/(Nat.factorial m*m) := by
  apply (foh_defect_certificate a b Y n m hT hY0 hY hr hr1 hm).trans
  have hnonneg : 0 ≤ (‖a‖+T*‖b‖)*T := by positivity
  have he := ExponentialCertificate.scalar_bound hnonneg hshort l hl
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right he
    (mul_nonneg (fohDefectRadius_nonneg a b n hT) hT))) le_rfl

/-- Polynomial whose evaluation is the retained FOH exponent. -/
def fohExponentPolynomial (a b : A) : Polynomial A :=
  Polynomial.monomial 1 a + Polynomial.monomial 2 ((1/2:ℝ) • b) +
  Polynomial.monomial 3 ((1/12:ℝ) • comm a b)

/-- The finite polynomial difference retains all cancellations, and its
coefficients can be computed using rational arithmetic for rational data. -/
def fohFiniteDifference (a b : A) (n m : ℕ) : Polynomial A :=
  (∑ k ∈ range (n+1), Polynomial.monomial k (flowCoeff a b 0 k)) -
  ∑ j ∈ range m, ((Nat.factorial j:ℝ)⁻¹) • (fohExponentPolynomial a b)^j

omit [CompleteSpace A] in
theorem fohExponentPolynomial_value (a b : A) (t : ℝ) :
    AlgebraPolynomial.value (fohExponentPolynomial a b) t = fohRetainedExponent a b t := by
  simp only [fohExponentPolynomial, AlgebraPolynomial.value_add,
    AlgebraPolynomial.value_monomial, smul_smul, pow_one, fohRetainedExponent]
  congr 2 <;> congr 1 <;> ring

omit [CompleteSpace A] in
theorem fohFiniteDifference_value (a b : A) (n m : ℕ) (t : ℝ) :
    AlgebraPolynomial.value (fohFiniteDifference a b n m) t =
      fohTaylor a b n t - ExponentialCertificate.polynomial (fohRetainedExponent a b t) m := by
  simp only [fohFiniteDifference, AlgebraPolynomial.value_sub, AlgebraPolynomial.value_sum,
    AlgebraPolynomial.value_monomial, AlgebraPolynomial.value_smul, AlgebraPolynomial.value_pow,
    fohExponentPolynomial_value, fohTaylor, ExponentialCertificate.polynomial]

/-- Complete certificate in the stable coefficientwise form. Every term
on the right depends only on the two input coefficients and chosen finite
orders; there is no fitted or assumed higher-order remainder. -/
theorem foh_defect_coefficient_certificate [NormOneClass A]
    (a b : A) (Y : ℝ → A) (n m : ℕ) {T r : ℝ}
    (hT : 0 ≤ T) (hY0 : Y 0 = 1)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (Y t*(a+t • b)) t)
    (hr : ‖fohRetainedExponent a b T‖ ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) :
    ‖Y T-NormedSpace.exp (fohRetainedExponent a b T)‖ ≤
      AlgebraPolynomial.majorant (fohFiniteDifference a b n m) T +
      Real.exp ((‖a‖+T*‖b‖)*T) * (fohDefectRadius a b n T*T) +
      r^m*(m+1)/(Nat.factorial m*m) := by
  apply (foh_defect_certificate a b Y n m hT hY0 hY hr hr1 hm).trans
  have hb := AlgebraPolynomial.norm_value_le (fohFiniteDifference a b n m)
    (show |T| ≤ T by rw [abs_of_nonneg hT])
  rw [fohFiniteDifference_value] at hb
  exact add_le_add (add_le_add hb le_rfl) le_rfl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
omit [CompleteSpace A] in
/-- Exact agreement through degree four for the retained exponent itself. -/
theorem fohExponentPolynomial_exp_coeff (a b : A) (k : ℕ) (hk : k ≤ 4) :
    expCoeff (fohExponentPolynomial a b) k = flowCoeff a b 0 k := by
  interval_cases k <;>
    norm_num [expCoeff, fohExponentPolynomial, flowCoeff, pow_succ, Polynomial.coeff_mul,
      Polynomial.coeff_monomial, Polynomial.coeff_one,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] <;>
    magnus_nc

omit [CompleteSpace A] in
/-- Omitted exponential powers cannot affect a lower time coefficient. -/
theorem foh_truncated_exp_coeff (p : Polynomial A) (hp : p.coeff 0 = 0)
    (m k : ℕ) (hkm : k < m) :
    (∑ j ∈ range m, ((Nat.factorial j:ℝ)⁻¹) • p^j).coeff k = expCoeff p k := by
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul]
  have hm : m = k+1+(m-(k+1)) := by omega
  rw [hm, sum_range_add]
  have hz : ∑ j ∈ range (m-(k+1)),
      ((Nat.factorial (k+1+j):ℝ)⁻¹) • (p^(k+1+j)).coeff k = 0 := by
    apply sum_eq_zero
    intro j _
    rw [coeff_pow_vanishes p hp (k+1+j) k (by omega), smul_zero]
  rw [hz, add_zero]
  rfl

omit [CompleteSpace A] in
/-- The stable finite-difference evaluation may set degrees zero through
four to exact zero. This is a proved cancellation, not a floating-point
threshold applied to unverified coefficients. -/
theorem fohFiniteDifference_low_coeff (a b : A) (n m k : ℕ)
    (hn : 4 ≤ n) (hm : 5 ≤ m) (hk : k ≤ 4) :
    (fohFiniteDifference a b n m).coeff k = 0 := by
  have hkm : k < m := by omega
  have hp : (fohExponentPolynomial a b).coeff 0 = 0 := by
    simp [fohExponentPolynomial, Polynomial.coeff_monomial]
  rw [fohFiniteDifference, Polynomial.coeff_sub, foh_truncated_exp_coeff _ hp m k hkm,
    fohExponentPolynomial_exp_coeff a b k hk]
  have hkn : k < n+1 := by omega
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hkn]

end GNC.Magnus
