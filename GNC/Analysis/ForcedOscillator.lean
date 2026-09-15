import GNC.Analysis.QuadraticModes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Exact cosine forcing of a stable scalar oscillator. The denominator
condition excludes resonance explicitly. A classical modal method and a
phase-retaining geometric method evaluate the identical response. -/
noncomputable section
namespace GNC.ForcedOscillator
open Real

def position (a ν ω t : ℝ) : ℝ := a*(cos (ν*t)-cos (ω*t))/(ω^2-ν^2)
def velocity (a ν ω t : ℝ) : ℝ := a*(ω*sin (ω*t)-ν*sin (ν*t))/(ω^2-ν^2)

theorem derivative_position (a ν ω t : ℝ) :
    HasDerivAt (position a ν ω) (velocity a ν ω t) t := by
  convert (((((hasDerivAt_id t).const_mul ν).cos).sub
    (((hasDerivAt_id t).const_mul ω).cos)).const_mul a).div_const (ω^2-ν^2) using 1 <;>
    dsimp [position,velocity] <;> ring

theorem derivative_velocity (a ν ω t : ℝ) (h : ω^2-ν^2 ≠ 0) :
    HasDerivAt (velocity a ν ω) (-ν^2*position a ν ω t+a*cos (ω*t)) t := by
  convert (((((hasDerivAt_id t).const_mul ω).sin.const_mul ω).sub
    (((hasDerivAt_id t).const_mul ν).sin.const_mul ν)).const_mul a).div_const (ω^2-ν^2)
    using 1 <;> dsimp [velocity,position] <;> field_simp <;> ring

theorem initial (a ν ω : ℝ) : position a ν ω 0=0 ∧ velocity a ν ω 0=0 := by
  simp [position,velocity]

/-- The difference from integrating the thrust alone. Gravity's stable
mode is retained, and its effect is bounded rather than silently dropped. -/
theorem velocity_minus_free (a ν ω t : ℝ) (hω : ω ≠ 0) (h : ω^2-ν^2 ≠ 0) :
    velocity a ν ω t-a*sin (ω*t)/ω =
      a/(ω^2-ν^2)*(ν^2/ω*sin (ω*t)-ν*sin (ν*t)) := by
  unfold velocity
  field_simp
  ring

theorem velocity_minus_free_bound {a ν ω : ℝ} (ha : 0≤a) (hν : 0≤ν)
    (hω : 0<ω) (h : ν^2<ω^2) (t : ℝ) :
    |velocity a ν ω t-a*sin (ω*t)/ω| ≤ a/(ω^2-ν^2)*(ν^2/ω+ν) := by
  rw [velocity_minus_free a ν ω t hω.ne' (sub_pos.mpr h).ne',abs_mul,
    abs_of_nonneg (div_nonneg ha (sub_pos.mpr h).le)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg ha (sub_pos.mpr h).le)
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg ν) hω.le),abs_of_nonneg hν]
  nlinarith [Real.abs_sin_le_one (ω*t),Real.abs_sin_le_one (ν*t),
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (ω*t)) (div_nonneg (sq_nonneg ν) hω.le),
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (ν*t)) hν]

end GNC.ForcedOscillator
