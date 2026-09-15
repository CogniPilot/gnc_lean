import GNC.Analysis.ExponentialCertificate
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul

/-! Real-time polynomials with possibly noncommuting algebra coefficients.
Evaluation uses the central scalar t times the identity. This makes finite
coefficient identities usable as actual differentiable matrix witnesses.
-/
noncomputable section
namespace GNC.AlgebraPolynomial
open Polynomial Finset
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def value (p : Polynomial A) (t : ℝ) : A := p.eval (t • (1:A))

theorem value_C (a : A) (t : ℝ) : value (C a) t = a := Polynomial.eval_C

theorem value_add (p q : Polynomial A) (t : ℝ) :
    value (p+q) t = value p t+value q t := Polynomial.eval_add

theorem value_sub (p q : Polynomial A) (t : ℝ) :
    value (p-q) t = value p t-value q t := Polynomial.eval_sub _ _ _

theorem value_smul (p : Polynomial A) (r t : ℝ) :
    value (r • p) t = r • value p t := Polynomial.eval_smul r p _

theorem value_mul (p q : Polynomial A) (t : ℝ) :
    value (p*q) t = value p t*value q t :=
  Polynomial.eval₂_mul_noncomm (RingHom.id A) (t • (1:A))
    (fun k => (Commute.one_right (q.coeff k)).smul_right t)

theorem value_pow (p : Polynomial A) (t : ℝ) (n : ℕ) :
    value (p^n) t = (value p t)^n := by
  induction n with
  | zero => simp [value]
  | succ n ih => simp only [pow_succ, value_mul, ih]

theorem value_monomial (a : A) (n : ℕ) (t : ℝ) :
    value (monomial n a) t = (t^n) • a := by
  simp [value, Polynomial.eval_monomial, smul_pow]

theorem value_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial A) (t : ℝ) :
    value (∑ i ∈ s, p i) t = ∑ i ∈ s, value (p i) t := by
  simp [value, Polynomial.eval_finset_sum]

theorem value_coefficients (p : Polynomial A) (t : ℝ) :
    value p t = ∑ k ∈ p.support, (t^k) • p.coeff k := by
  simp [value, Polynomial.eval_eq_sum, Polynomial.sum, smul_pow]

theorem hasDerivAt_value (p : Polynomial A) (t : ℝ) :
    HasDerivAt (value p) (value p.derivative t) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext u; exact value_add p q u
    · simp only [map_add, value_add]
  | monomial n a =>
    have h := (hasDerivAt_pow n t).smul_const a
    convert h using 1
    · funext u; exact value_monomial a n u
    · rw [Polynomial.derivative_monomial, value_monomial]
      have hn : a*(n:A) = (n:ℝ) • a := by
        rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
        exact (Nat.cast_commute n a).eq.symm
      rw [hn, smul_smul]
      congr 1; ring

/-- A finite weighted absolute coefficient sum. In a concrete matrix norm
the coefficient norms also need finite, justified upper bounds. -/
def majorant (p : Polynomial A) (r : ℝ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖*r^k

omit [NormedAlgebra ℝ A] in
theorem majorant_nonnegative (p : Polynomial A) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ majorant p r := by unfold majorant; positivity

theorem norm_value_le (p : Polynomial A) {t r : ℝ} (ht : |t| ≤ r) :
    ‖value p t‖ ≤ majorant p r := by
  rw [value_coefficients]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg t) ht k) (norm_nonneg (p.coeff k))

/-- Low vanishing coefficients yield a proved power of the step length,
not merely a formal order statement. -/
theorem vanishing_bound (p : Polynomial A) (m : ℕ)
    (hz : ∀ k < m, p.coeff k = 0) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖value p t‖ ≤ t^m*majorant p 1 := by
  apply (norm_value_le p (show |t| ≤ t by rw [abs_of_nonneg h0])).trans
  unfold majorant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkm : m ≤ k := by
    by_contra h
    have hc := hz k (by omega)
    exact (Polynomial.mem_support_iff.mp hk) hc
  have hpow : t^k ≤ t^m := by
    rw [show k = m+(k-m) by omega, pow_add]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (pow_nonneg h0 m)).trans_eq (mul_one _)
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow (norm_nonneg (p.coeff k))

end GNC.AlgebraPolynomial
