import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Exact regression family for uncertainty truncation in validated ODEs.
The time dependence is affine, but omitting an uncertainty monomial still
requires a nonzero remainder. This proves the mathematical test oracle;
it does not formalize any external Taylor-model implementation. -/
namespace GNC.UncertaintyTruncation
noncomputable section
open Polynomial Set

def field (m : ℕ) (x : ℝ × ℝ) : ℝ × ℝ := (x.2 ^ m, 0)
def flow (m : ℕ) (u t : ℝ) : ℝ × ℝ := (t * u ^ m, u)

theorem derivative (m : ℕ) (u t : ℝ) :
    HasDerivAt (flow m u) (field m (flow m u t)) t := by
  simpa [flow, field] using
    ((hasDerivAt_id t).mul_const (u ^ m)).prodMk (hasDerivAt_const t u)

theorem initial (m : ℕ) (u : ℝ) : flow m u 0 = (0, u) := by
  simp [flow]

/-- The degree-n uncertainty jet of the exact first component. -/
def jet (n m : ℕ) (t u : ℝ) : ℝ :=
  t * ∑ k ∈ Finset.range (n + 1), (X ^ m : Polynomial ℝ).coeff k * u ^ k

theorem jet_zero {n m : ℕ} (h : n < m) (t u : ℝ) : jet n m t u = 0 := by
  have hs : ∀ k ∈ Finset.range (n + 1),
      (X ^ m : Polynomial ℝ).coeff k * u ^ k = 0 := by
    intro k hk
    have hkm : k ≠ m := by have := Finset.mem_range.mp hk; omega
    simp [coeff_X_pow, hkm]
  unfold jet
  rw [Finset.sum_eq_zero hs, mul_zero]

theorem exact_error {n m : ℕ} (h : n < m) (t u : ℝ) :
    |(flow m u t).1 - jet n m t u| = |t| * |u| ^ m := by
  simp [flow, jet_zero h, abs_mul, abs_pow]

theorem error_le {n m : ℕ} (h : n < m) (t : ℝ) {u : ℝ} (hu : |u| ≤ 1) :
    |(flow m u t).1 - jet n m t u| ≤ |t| := by
  rw [exact_error h]
  exact mul_le_of_le_one_right (abs_nonneg t) (pow_le_one₀ (abs_nonneg u) hu)

theorem error_at_one {n m : ℕ} (h : n < m) (t : ℝ) :
    |(flow m 1 t).1 - jet n m t 1| = |t| := by
  simp [exact_error h]

/-- The uniform remainder must be at least |t|, even though all retained
uncertainty coefficients and all time derivatives above degree one vanish. -/
theorem enclosure_requires_radius {n m : ℕ} (h : n < m) (t radius : ℝ)
    (hb : ∀ u ∈ Icc (-1 : ℝ) 1, |(flow m u t).1 - jet n m t u| ≤ radius) :
    |t| ≤ radius := by
  simpa [error_at_one h] using hb 1 (by constructor <;> norm_num)

theorem cubic_zero_enclosure_false :
    ¬ (∀ u ∈ Icc (-1 : ℝ) 1, (flow 3 u 1).1 ∈ Icc (0 : ℝ) 0) := by
  intro h
  have := h 1 (by constructor <;> norm_num)
  norm_num [flow] at this

theorem cubic_jet_radius {radius : ℝ}
    (hb : ∀ u ∈ Icc (-1 : ℝ) 1, |(flow 3 u 1).1 - jet 2 3 1 u| ≤ radius) :
    1 ≤ radius := by
  simpa using enclosure_requires_radius (by norm_num : 2 < 3) 1 radius hb

end
end GNC.UncertaintyTruncation
