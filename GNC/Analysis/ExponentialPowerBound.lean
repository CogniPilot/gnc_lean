import GNC.Analysis.ExponentialCertificate
import Mathlib.Analysis.SpecificLimits.Normed

/-! An exponential remainder bound retaining the first omitted matrix power.
This preserves cancellations, including nilpotence, before applying a norm.
The factorial majorant and convergent geometric series are from mathlib.
-/
noncomputable section
namespace GNC.ExponentialCertificate
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormOneClass A]

/-- The first omitted power is retained exactly. Replacing it by a power
of the norm would lose matrix cancellations before estimating the tail. -/
theorem remainder_bound_power (x : A) (hx : ‖x‖ ≤ 1) (n : ℕ) (hn : 0 < n) :
    ‖NormedSpace.exp x-polynomial x n‖ ≤ ‖x^n‖*(n+1)/(Nat.factorial n*n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hfac : (0:ℝ) < n.factorial := by positivity
  have hq : ‖(1:ℝ)/(n+1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hs := (hasSum_geometric_of_norm_lt_one hq).mul_left (‖x^n‖/(n.factorial:ℝ))
  have hm := (hasSum_nat_add_iff' n).mpr
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have hb : ‖NormedSpace.exp x-polynomial x n‖ ≤
      (‖x^n‖/(n.factorial:ℝ))*(1-(1:ℝ)/(n+1))⁻¹ := by
    apply hm.norm_le_of_bounded hs
    intro k
    have hf : (n.factorial:ℝ)*(n+1)^k ≤ (k+n).factorial := by
      exact_mod_cast (show n.factorial*(n+1)^k ≤ (k+n).factorial by
        simpa only [Nat.add_comm] using (Nat.factorial_mul_pow_le_factorial (m := n) (n := k)))
    have hp : ‖x^(k+n)‖ ≤ ‖x^n‖ := by
      rw [Nat.add_comm k n, pow_add]
      have hpk : ‖x^k‖ ≤ 1 := (norm_pow_le x k).trans (by
        simpa using (pow_le_pow_left₀ (norm_nonneg x) hx k))
      exact (norm_mul_le _ _).trans
        ((mul_le_mul_of_nonneg_left hpk (norm_nonneg _)).trans_eq (mul_one _))
    calc
      ‖((Nat.factorial (k+n):ℝ)⁻¹) • x^(k+n)‖ = ‖x^(k+n)‖/((k+n).factorial:ℝ) := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity)]
        ring
      _ ≤ ‖x^n‖/((k+n).factorial:ℝ) := div_le_div_of_nonneg_right hp (by positivity)
      _ ≤ ‖x^n‖/((n.factorial:ℝ)*(n+1)^k) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hf
      _ = (‖x^n‖/(n.factorial:ℝ))*((1:ℝ)/(n+1))^k := by rw [div_pow]; ring
  apply hb.trans_eq
  field_simp [ne_of_gt hnR, ne_of_gt hfac]; ring

/-- A nilpotent omitted power makes the actual exponential equal to its
finite polynomial under the same step-norm condition. -/
theorem exact_of_omitted_power_zero (x : A) (hx : ‖x‖ ≤ 1) (n : ℕ) (hn : 0 < n)
    (hz : x^n = 0) : NormedSpace.exp x = polynomial x n := by
  have h := remainder_bound_power x hx n hn
  simpa [hz, norm_le_zero_iff, sub_eq_zero] using h

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
/-- Retaining the actual power never increases this exponential-tail
budget relative to taking the matrix norm before the power. This is a
comparison of these two bounds, not of complete numerical algorithms. -/
theorem power_budget_le_norm_budget (x : A) (n : ℕ) :
    ‖x^n‖*(n+1)/(Nat.factorial n*n) ≤ ‖x‖^n*(n+1)/(Nat.factorial n*n) := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (norm_pow_le x n) (by positivity)) (by positivity)

omit [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] in
theorem power_budget_strict (x : A) (n : ℕ) (hn : 0 < n)
    (hc : ‖x^n‖ < ‖x‖^n) :
    ‖x^n‖*(n+1)/(Nat.factorial n*n) < ‖x‖^n*(n+1)/(Nat.factorial n*n) := by
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hc (by positivity)) (by positivity)

end GNC.ExponentialCertificate
