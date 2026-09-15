import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Bound the actual normed-algebra exponential using released mathlib's
convergent series and scalar remainder theorem. This provides a certificate
for an exponential evaluation at a supplied exact exponent; uncertainty in
that exponent and Magnus truncation are separate obligations. -/
noncomputable section
open Finset
namespace GNC.ExponentialCertificate
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

def polynomial (x : A) (n : ℕ) : A :=
  ∑ k ∈ range n, ((Nat.factorial k : ℝ)⁻¹) • x^k

def scalarPolynomial (r : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, r^k/(Nat.factorial k : ℝ)

theorem scalar_series (r : ℝ) :
    HasSum (fun k : ℕ => r^k/(Nat.factorial k : ℝ)) (Real.exp r) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) r
  simpa [Real.exp_eq_exp_ℝ, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- An upper bound with only finite arithmetic when the inputs are rational. -/
theorem scalar_bound {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (n : ℕ) (hn : 0 < n) :
    Real.exp r ≤ scalarPolynomial r n+r^n*(n+1)/(Nat.factorial n*n) :=
  Real.exp_bound' h0 h1 hn

/-- Matrix powers are bounded termwise; completeness and the norm-one
identity make the actual exponential tail obey the scalar tail bound. -/
theorem remainder_le_scalar (x : A) {r : ℝ} (hx : ‖x‖ ≤ r) (n : ℕ) :
    ‖NormedSpace.exp x-polynomial x n‖ ≤ Real.exp r-scalarPolynomial r n := by
  have hm := (hasSum_nat_add_iff' n).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hs := (hasSum_nat_add_iff' n).mpr (scalar_series r)
  apply hm.norm_le_of_bounded hs
  intro k
  rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (k+n).factorial)]
  rw [div_eq_mul_inv, mul_comm (r^(k+n))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_pow_le x (k+n)).trans (pow_le_pow_left₀ (norm_nonneg x) hx (k+n))

/-- A rational expression bounds the true exponential remainder when the
supplied norm radius is at most one. No floating-point exponential is trusted. -/
theorem remainder_bound (x : A) {r : ℝ} (hx : ‖x‖ ≤ r) (hr : r ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    ‖NormedSpace.exp x-polynomial x n‖ ≤
      r^n*(n+1)/(Nat.factorial n*n) := by
  have h := Real.exp_bound' ((norm_nonneg x).trans hx) hr hn
  have hs := remainder_le_scalar x hx n
  change Real.exp r ≤ scalarPolynomial r n+r^n*(n+1)/(Nat.factorial n*n) at h
  linarith

/-- Compare an untrusted reported exponential with an exact finite
polynomial, then include the proved analytic tail. -/
theorem evaluation_bound (x reported : A) {r rounding : ℝ}
    (hx : ‖x‖ ≤ r) (hr : r ≤ 1) (n : ℕ) (hn : 0 < n)
    (hreported : ‖reported-polynomial x n‖ ≤ rounding) :
    ‖reported-NormedSpace.exp x‖ ≤ rounding+r^n*(n+1)/(Nat.factorial n*n) := by
  have h := remainder_bound x hx hr n hn
  calc
    ‖reported-NormedSpace.exp x‖ ≤
      ‖reported-polynomial x n‖+‖polynomial x n-NormedSpace.exp x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ rounding+r^n*(n+1)/(Nat.factorial n*n) := by
      rw [norm_sub_rev (polynomial x n)]
      exact add_le_add hreported h

theorem norm_exp_le (x : A) {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖NormedSpace.exp x‖ ≤ Real.exp r := by
  simpa [polynomial, scalarPolynomial] using remainder_le_scalar x hx 0

/-- Perturbing an exponent does not require the two exponents to commute.
The proof differentiates a product of two one-parameter exponentials. -/
theorem perturbation_bound (x y : A) {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖NormedSpace.exp x-NormedSpace.exp y‖ ≤ Real.exp r * ‖x-y‖ := by
  let f := fun t : ℝ => NormedSpace.exp ((1-t) • x) * NormedSpace.exp (t • y)
  let df := fun t : ℝ =>
    NormedSpace.exp ((1-t) • x) * (y-x) * NormedSpace.exp (t • y)
  have hd (t : ℝ) : HasDerivAt f (df t) t := by
    have hl := (hasDerivAt_exp_smul_const x (1-t)).scomp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    have hr := hasDerivAt_exp_smul_const' y t
    convert hl.mul hr using 1
    simp only [zero_sub, neg_one_smul]
    dsimp [df]
    noncomm_ring
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖df t‖ ≤ Real.exp r * ‖x-y‖ := by
    have htn : 0 ≤ t := ht.1
    have hsn : 0 ≤ 1-t := sub_nonneg.mpr ht.2.le
    have hxl : ‖(1-t) • x‖ ≤ (1-t)*r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsn]
      exact mul_le_mul_of_nonneg_left hx hsn
    have hyl : ‖t • y‖ ≤ t*r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htn]
      exact mul_le_mul_of_nonneg_left hy htn
    calc
      ‖df t‖ ≤
          ‖NormedSpace.exp ((1-t) • x)‖ * ‖y-x‖ * ‖NormedSpace.exp (t • y)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Real.exp ((1-t)*r) * ‖y-x‖ * Real.exp (t*r) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (norm_exp_le _ hxl) (norm_nonneg _))
          (norm_exp_le _ hyl) (norm_nonneg _) (by positivity)
      _ = Real.exp r * ‖x-y‖ := by
        rw [norm_sub_rev y x]
        calc
          _ = (Real.exp ((1-t)*r) * Real.exp (t*r)) * ‖x-y‖ := by ring
          _ = Real.exp r * ‖x-y‖ := by rw [← Real.exp_add]; congr 2; ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) hb
  simpa [f, NormedSpace.exp_zero, norm_sub_rev] using h

/-- The evaluator's error and uncertainty in the exponent are separate.
The latter is propagated by a proved bound for the actual exponential. -/
theorem uncertain_evaluation_bound (x exact reported : A) {r rounding inputError : ℝ}
    (hx : ‖x‖ ≤ r) (he : ‖exact‖ ≤ r) (hr : r ≤ 1)
    (n : ℕ) (hn : 0 < n) (hi : ‖x-exact‖ ≤ inputError)
    (hreported : ‖reported-polynomial x n‖ ≤ rounding) :
    ‖reported-NormedSpace.exp exact‖ ≤
      rounding+r^n*(n+1)/(Nat.factorial n*n)+Real.exp r*inputError := by
  calc
    ‖reported-NormedSpace.exp exact‖ ≤
        ‖reported-NormedSpace.exp x‖+‖NormedSpace.exp x-NormedSpace.exp exact‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ rounding+r^n*(n+1)/(Nat.factorial n*n)+Real.exp r*inputError :=
      add_le_add (evaluation_bound x reported hx hr n hn hreported)
        ((perturbation_bound x exact hx he).trans
          (mul_le_mul_of_nonneg_left hi (Real.exp_pos r).le))

/-- The combined evaluation/perturbation bound can itself be evaluated with
finite arithmetic. The input-error bound forces `inputError` nonnegative. -/
theorem uncertain_evaluation_bound_finite (x exact reported : A)
    {r rounding inputError : ℝ} (hx : ‖x‖ ≤ r) (he : ‖exact‖ ≤ r) (hr : r ≤ 1)
    (n : ℕ) (hn : 0 < n) (hi : ‖x-exact‖ ≤ inputError)
    (hreported : ‖reported-polynomial x n‖ ≤ rounding) :
    ‖reported-NormedSpace.exp exact‖ ≤
      rounding+r^n*(n+1)/(Nat.factorial n*n)+
        (scalarPolynomial r n+r^n*(n+1)/(Nat.factorial n*n))*inputError := by
  apply (uncertain_evaluation_bound x exact reported hx he hr n hn hi hreported).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (scalar_bound ((norm_nonneg x).trans hx) hr n hn) ((norm_nonneg _).trans hi))

end GNC.ExponentialCertificate
