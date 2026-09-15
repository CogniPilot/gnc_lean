import GNC.Magnus.GaussError
import GNC.Analysis.AlgebraPolynomial
import GNC.Analysis.ExponentialStep
import GNC.Analysis.ExponentialPowerBound

/-! From the finite Gauss coefficient identities to a quantitative analytic
local remainder. The ODE witness and its differential residual are explicit
polynomials with noncommuting coefficients; the matrix exponential itself
is bounded using the convergent series from released mathlib.
-/
noncomputable section
namespace GNC.Magnus.GaussRemainder
open Polynomial Finset AlgebraPolynomial
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def generator (a b c d : A) : Polynomial A :=
  monomial 0 a+monomial 1 b+monomial 2 c+monomial 3 d

def witness (a b c d : A) : Polynomial A :=
  ∑ k ∈ range 5, monomial k (leftFlowCoeff a b c d k)

def polynomialExponential (p : Polynomial A) (n : ℕ) : Polynomial A :=
  ∑ k ∈ range n, ((Nat.factorial k:ℝ)⁻¹) • p^k

def mismatch (a b c d : A) : Polynomial A :=
  polynomialExponential (gaussLeftExponent a b c d (Real.sqrt 3/6)) 5-witness a b c d

def residual (a b c d : A) : Polynomial A :=
  (witness a b c d).derivative-generator a b c d*witness a b c d

theorem value_polynomialExponential (p : Polynomial A) (n : ℕ) (t : ℝ) :
    value (polynomialExponential p n) t =
      ExponentialCertificate.polynomial (value p t) n := by
  simp only [polynomialExponential, value_sum, value_smul, value_pow,
    ExponentialCertificate.polynomial]

theorem witness_coeff (a b c d : A) (k : ℕ) (hk : k < 5) :
    (witness a b c d).coeff k = leftFlowCoeff a b c d k := by
  classical
  simp [witness, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hk]

theorem polynomialExponential_coeff (p : Polynomial A) (hp : p.coeff 0 = 0)
    (n k : ℕ) (hk : k < n) :
    (polynomialExponential p n).coeff k = expCoeff p k := by
  simp only [polynomialExponential, Polynomial.finset_sum_coeff, Polynomial.coeff_smul,
    expCoeff]
  symm
  apply Finset.sum_subset
  · intro i hi
    exact mem_range.mpr (by have := mem_range.mp hi; omega)
  · intro i hi hnot
    have hki : k < i := by have := mem_range.mp hi; simp only [mem_range] at hnot; omega
    rw [coeff_pow_vanishes p hp i k hki, smul_zero]

theorem mismatch_vanishes (a b c d : A) (k : ℕ) (hk : k < 5) :
    (mismatch a b c d).coeff k = 0 := by
  rw [mismatch, Polynomial.coeff_sub,
    polynomialExponential_coeff _ (gauss_left_constant a b c d) 5 k hk,
    witness_coeff a b c d k hk, gauss_left_flow_coeff a b c d k (by omega), sub_self]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem residual_vanishes (a b c d : A) (k : ℕ) (hk : k < 4) :
    (residual a b c d).coeff k = 0 := by
  rw [residual, Polynomial.coeff_sub, Polynomial.coeff_derivative,
    witness_coeff a b c d (k+1) (by omega), Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hn (v : A) (n : ℕ) : v*(n:A) = (n:ℝ) • v := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    exact (Nat.cast_commute n v).eq.symm
  rw [show (k:A)+1 = ((k+1:ℕ):A) by push_cast; rfl, hn]
  interval_cases k <;>
    norm_num [generator, Polynomial.coeff_monomial, Finset.sum_range_succ,
      witness_coeff, leftFlowCoeff, pow_succ] <;> magnus_nc

theorem witness_initial (a b c d : A) : value (witness a b c d) 0 = 1 := by
  simp only [value, zero_smul, ← Polynomial.coeff_zero_eq_eval_zero]
  rw [witness_coeff a b c d 0 (by omega)]
  simp [leftFlowCoeff]

/-- The actual derivative of the polynomial witness has exactly the stored
polynomial residual. This is an analytic derivative theorem, not a jet. -/
theorem witness_derivative (a b c d : A) (t : ℝ) :
    HasDerivAt (value (witness a b c d))
      (value (generator a b c d) t*value (witness a b c d) t+
        value (residual a b c d) t) t := by
  convert hasDerivAt_value (witness a b c d) t using 1
  simp only [residual, value_sub, value_mul]
  abel

theorem node_value (a b c d : A) (s h : ℝ) :
    value (nodeSample a b c d s) h = value (generator a b c d) (s*h) := by
  simp only [nodeSample, generator, value_add, value_monomial, pow_zero, pow_one,
    one_smul, smul_smul]
  simp only [mul_pow, mul_comm]

/-- The audited polynomial is exactly the standard two-node matrix formula
applied to this cubic generator, including the actual Gauss sampling times. -/
theorem exponent_value (a b c d : A) (h : ℝ) :
    value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h =
      gaussStepExponent
        (value (generator a b c d) ((1/2-Real.sqrt 3/6)*h))
        (value (generator a b c d) ((1/2+Real.sqrt 3/6)*h)) h := by
  have he := gaussStepExponent_eq_eval a b c d h
  change value _ h = gaussStepExponent (value _ h) (value _ h) h at he
  simpa only [node_value] using he

theorem exponent_norm (a b c d : A) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ‖value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h‖ ≤
      h*majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1 := by
  simpa only [pow_one] using vanishing_bound
    (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1
    (fun k hk => by
      have hk0 : k = 0 := by omega
      subst k
      exact gauss_left_constant a b c d) h0 h1

/-- An actual exponential remainder bound relative to the explicit ODE
witness. The factor 1/100 is 6/(5! * 5), from the proved geometric tail
majorant; it is not a numerical allowance. The first omitted polynomial
power is retained, so nilpotence can make this tail exactly zero. All other
constants are exact finite coefficient sums. -/
theorem exponential_witness_error [CompleteSpace A] [NormOneClass A]
    (a b c d : A) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hsmall : h*majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1 ≤ 1) :
    ‖NormedSpace.exp (value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h)-
      value (witness a b c d) h‖ ≤
      h^5*(majorant ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5) 1/100+
        majorant (mismatch a b c d) 1) := by
  let p := gaussLeftExponent a b c d (Real.sqrt 3/6)
  have ht := ExponentialCertificate.remainder_bound_power (value p h)
    ((exponent_norm a b c d h0 h1).trans hsmall) 5 (by omega)
  have hp := vanishing_bound (p^5) 5
    (fun k hk => coeff_pow_vanishes p (gauss_left_constant a b c d) 5 k hk) h0 h1
  rw [value_pow] at hp
  have htail := ht.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ (5:ℕ)+1))
    (by positivity : (0:ℝ) ≤ (Nat.factorial 5:ℝ)*5))
  have hm := vanishing_bound (mismatch a b c d) 5 (mismatch_vanishes a b c d) h0 h1
  have he : ExponentialCertificate.polynomial (value p h) 5-value (witness a b c d) h =
      value (mismatch a b c d) h := by
    simp only [mismatch, value_sub, value_polynomialExponential, p]
  calc
    _ ≤ ‖NormedSpace.exp (value p h)-ExponentialCertificate.polynomial (value p h) 5‖+
        ‖ExponentialCertificate.polynomial (value p h) 5-value (witness a b c d) h‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ h^5*majorant (p^5) 1*(5+1)/(Nat.factorial 5*5)+
        h^5*majorant (mismatch a b c d) 1 := by rw [he]; exact add_le_add htail hm
    _ = _ := by norm_num [Nat.factorial]; ring

section Analytic
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V] [Nontrivial V]
local notation "End" => V →L[ℝ] V

/-- A complete analytic local truncation bound for the two-node Gauss
Magnus rule and a cubic generator. The finite cancellations, polynomial
derivative, exponential tail and ODE comparison are all proved above.
This theorem does not yet bound a nonpolynomial reference's cubic remainder
or the errors of a floating-point evaluator. -/
theorem cubic_local_error (a b c d : End) (Q : ℝ → End)
    {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hsmall : h*majorant (gaussLeftExponent a b c d (Real.sqrt 3/6)) 1 ≤ 1)
    (hQ : ∀ t ∈ Set.Icc 0 h, HasDerivAt Q (value (generator a b c d) t*Q t) t)
    (hinit : Q 0 = 1) :
    ‖NormedSpace.exp (value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h)-Q h‖ ≤
      h^5*(majorant ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5) 1/100+
        majorant (mismatch a b c d) 1+
        majorant (residual a b c d) 1*Real.exp (majorant (generator a b c d) 1*h)) := by
  let L := majorant (generator a b c d) 1
  let R := majorant (residual a b c d) 1
  have hL : 0 ≤ L := majorant_nonnegative _ (by norm_num)
  have hR : 0 ≤ R := majorant_nonnegative _ (by norm_num)
  have hA (t : ℝ) (ht : t ∈ Set.Icc 0 h) : ‖value (generator a b c d) t‖ ≤ L :=
    norm_value_le _ (by rw [abs_of_nonneg ht.1]; exact ht.2.trans h1)
  have hD (t : ℝ) (ht : t ∈ Set.Icc 0 h) : ‖value (residual a b c d) t‖ ≤ h^4*R := by
    apply (vanishing_bound _ 4 (residual_vanishes a b c d) ht.1 (ht.2.trans h1)).trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.1 ht.2 4) hR
  have hw := STMComparison.defect_bound_of_generator_norm
    (value (generator a b c d)) (value (witness a b c d)) Q (value (residual a b c d))
    (fun t _ => witness_derivative a b c d t) hQ ((witness_initial a b c d).trans hinit.symm)
    hA hD h ⟨h0,le_rfl⟩
  simp only [sub_zero] at hw
  have hg := ArcGronwall.gronwall_upper (δ := 0) hL (mul_nonneg (pow_nonneg h0 4) hR) h0
  simp only [zero_add] at hg
  have he := exponential_witness_error a b c d h0 h1 hsmall
  calc
    _ ≤ ‖NormedSpace.exp (value (gaussLeftExponent a b c d (Real.sqrt 3/6)) h)-
          value (witness a b c d) h‖+‖value (witness a b c d) h-Q h‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ h^5*(majorant ((gaussLeftExponent a b c d (Real.sqrt 3/6))^5) 1/100+
        majorant (mismatch a b c d) 1)+(h^4*R*h)*Real.exp (L*h) :=
      add_le_add he (hw.trans hg)
    _ = _ := by dsimp [R,L]; ring

end Analytic

end GNC.Magnus.GaussRemainder
