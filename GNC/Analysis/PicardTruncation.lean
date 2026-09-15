import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
A Picard refinement must preserve polynomial truncation defects.

The scalar equation x' = x, x(0) = 1 isolates a failure mode in an external
Taylor-model checker. These theorems check the mathematics, not C++ semantics.
-/
noncomputable section
namespace GNC.PicardTruncation

/-- The degree-two candidate for x' = x with unit initial value. -/
def quadratic (t : ℝ) : ℝ := 1 + t + t^2/2

/-- The exact Picard image of `quadratic`. -/
def picard (t : ℝ) : ℝ := 1 + t + t^2/2 + t^3/6

theorem quadratic_derivative (t : ℝ) :
    HasDerivAt quadratic (1+t) t := by
  convert (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).add
    (((hasDerivAt_id t).pow 2).div_const 2)) using 1 <;>
    dsimp [quadratic] <;> ring

theorem picard_derivative (t : ℝ) :
    HasDerivAt picard (quadratic t) t := by
  convert ((quadratic_derivative t).add
    (((hasDerivAt_id t).pow 3).div_const 6)) using 1 <;>
    dsimp [picard,quadratic] <;> ring

theorem initial_values : quadratic 0 = 1 ∧ picard 0 = 1 := by
  norm_num [quadratic,picard]

/-- Refinement with the original candidate must retain this forcing defect. -/
theorem differential_defect (t : ℝ) : quadratic t-(1+t) = t^2/2 := by
  unfold quadratic
  ring

/-- Truncating the degree-two term before integration hides this Picard defect. -/
theorem picard_defect (t : ℝ) : picard t-quadratic t = t^3/6 := by
  unfold picard quadratic
  ring

theorem picard_defect_bound {t h : ℝ} (ht : 0 ≤ t) (hth : t ≤ h) :
    |picard t-quadratic t| ≤ h^3/6 := by
  rw [picard_defect,abs_of_nonneg (by positivity)]
  gcongr

/-- Mathlib's exponential series supplies an independent lower error bound. -/
theorem exp_error_lower {t : ℝ} (ht : 0 ≤ t) :
    t^3/6 ≤ Real.exp t-quadratic t := by
  have h := Real.sum_le_exp_of_nonneg ht 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  dsimp [quadratic]
  linarith

theorem missing_tail_excludes_solution {t r : ℝ} (ht : 0 ≤ t)
    (hr : r < t^3/6) : quadratic t+r < Real.exp t := by
  have h := exp_error_lower ht
  linarith

/-- The exact binary64 upper endpoint observed in the unpatched scalar probe.
This is a statement about that stored number, not a verification of Flow*. -/
theorem observed_upper_excludes_solution :
    (7318349394477057:ℝ)/4503599627370496 < Real.exp (1/2) := by
  have h := exp_error_lower (t := (1:ℝ)/2) (by norm_num)
  norm_num [quadratic] at h
  linarith

/-- Keeping an additive defect gives the usual noniterative radius condition. -/
theorem closed_radius {h d : ℝ} (hh : h < 1) :
    h*(d/(1-h))+d = d/(1-h) := by
  field_simp [ne_of_gt (sub_pos.mpr hh)]
  ring

end GNC.PicardTruncation
