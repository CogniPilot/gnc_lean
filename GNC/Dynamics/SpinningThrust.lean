import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! Exact transverse response to constant-rate spinning thrust.
These are the thrust-response terms (or the complete error with spatially
uniform common gravity). Spatial gravity differences are not removed by
this calculation. No uncertainty or time series is truncated. -/
namespace GNC.SpinningThrust
noncomputable section

def velocityX (a ω t : ℝ) : ℝ := a * Real.sin (ω*t) / ω
def velocityY (a ω t : ℝ) : ℝ := a * (1-Real.cos (ω*t)) / ω
def positionX (a ω t : ℝ) : ℝ := a * (1-Real.cos (ω*t)) / ω^2
def positionY (a ω t : ℝ) : ℝ := a * (ω*t-Real.sin (ω*t)) / ω^2

theorem velocityX_derivative (a t : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (velocityX a ω) (a * Real.cos (ω*t)) t := by
  convert (((hasDerivAt_id t).const_mul ω).sin.const_mul a).div_const ω using 1 <;>
    dsimp [velocityX] <;> field_simp <;> ring

theorem velocityY_derivative (a t : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (velocityY a ω) (a * Real.sin (ω*t)) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_id t).const_mul ω).cos).const_mul a).div_const ω using 1 <;>
    dsimp [velocityY] <;> field_simp <;> ring

theorem positionX_derivative (a t : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (positionX a ω) (velocityX a ω t) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_id t).const_mul ω).cos).const_mul a).div_const (ω^2) using 1 <;>
    dsimp [positionX, velocityX] <;> field_simp <;> ring

theorem positionY_derivative (a t : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    HasDerivAt (positionY a ω) (velocityY a ω t) t := by
  convert ((((hasDerivAt_id t).const_mul ω).sub
    ((hasDerivAt_id t).const_mul ω).sin).const_mul a).div_const (ω^2) using 1 <;>
    dsimp [positionY, velocityY] <;> field_simp <;> ring

theorem initial (a ω : ℝ) :
    velocityX a ω 0 = 0 ∧ velocityY a ω 0 = 0 ∧
    positionX a ω 0 = 0 ∧ positionY a ω 0 = 0 := by
  simp [velocityX, velocityY, positionX, positionY]

theorem velocityX_bound (a ω t : ℝ) : |velocityX a ω t| ≤ |a| / |ω| := by
  simpa [velocityX, abs_div, abs_mul] using
    div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg a) (Real.abs_sin_le_one (ω*t)))
      (abs_nonneg ω)

theorem velocityX_uniform (a t : ℝ) {ω ωmin : ℝ}
    (hmin : 0 < ωmin) (hω : ωmin ≤ ω) :
    |velocityX a ω t| ≤ |a| / ωmin := by
  apply (velocityX_bound a ω t).trans
  rw [abs_of_pos (hmin.trans_le hω)]
  exact div_le_div_of_nonneg_left (abs_nonneg a) hmin hω

end
end GNC.SpinningThrust
