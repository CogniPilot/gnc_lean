import GNC.Planning.CoastInterpolation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Range and zero-derivative guarantees for coast interpolation.
These allow a reference path to be sampled during burns and traversed
smoothly between samples during the zero-thrust coasts. -/
noncomputable section
set_option autoImplicit false
namespace GNC.Planning
open Finset

theorem SmoothStep.value_bounds (u : ℝ) : 0 ≤ SmoothStep.value u ∧ SmoothStep.value u ≤ 1 := by
  have hm := monotone_of_hasDerivAt_nonneg SmoothStep.value_derivative
    (fun x => (SmoothStep.velocity_bounds x).1)
  by_cases h0 : u ≤ 0
  · rw [SmoothStep.value_before h0]; norm_num
  by_cases h1 : 1 ≤ u
  · rw [SmoothStep.value_after h1]; norm_num
  have ha := hm (show (0:ℝ) ≤ u by linarith)
  have hb := hm (show u ≤ (1:ℝ) by linarith)
  simpa [SmoothStep.value_before le_rfl, SmoothStep.value_after le_rfl] using And.intro ha hb

namespace CoastInterpolation

/-- Monotone key values keep every interpolated value in the key range,
even without assuming that the individual transition intervals are disjoint. -/
theorem value_bounds (keys starts durations : ℕ → ℝ) (N : ℕ) (t : ℝ)
    (hk : ∀ i < N, keys i ≤ keys (i+1)) :
    keys 0 ≤ value keys starts durations N t ∧ value keys starts durations N t ≤ keys N := by
  have hterm (i : ℕ) (hi : i ∈ range N) :
      0 ≤ SmoothStep.blend (starts i) (durations i) 0 (keys (i+1)-keys i) t ∧
      SmoothStep.blend (starts i) (durations i) 0 (keys (i+1)-keys i) t ≤ keys (i+1)-keys i := by
    have h := SmoothStep.value_bounds ((t-starts i)/durations i)
    have hd := sub_nonneg.mpr (hk i (mem_range.mp hi))
    simp only [SmoothStep.blend, sub_zero, zero_add]
    exact ⟨mul_nonneg hd h.1, by simpa using mul_le_mul_of_nonneg_left h.2 hd⟩
  have hl := sum_nonneg (fun i hi => (hterm i hi).1)
  have hu := sum_le_sum (fun i hi => (hterm i hi).2)
  rw [sum_range_sub] at hu
  dsimp only [value]
  constructor <;> linarith

/-- Both derivatives vanish on the closed holds, including the joins. -/
theorem jets_at_hold (keys starts durations : ℕ → ℝ) {N j : ℕ} {t : ℝ}
    (hd : ∀ i < N, 0 < durations i)
    (hpast : ∀ i < j, starts i+durations i ≤ t)
    (hfuture : ∀ i ∈ range N, j ≤ i → t ≤ starts i) :
    velocity keys starts durations N t = 0 ∧ acceleration keys starts durations N t = 0 := by
  have hz (i : ℕ) (hi : i ∈ range N) :
      SmoothStep.velocity ((t-starts i)/durations i) = 0 ∧
      SmoothStep.acceleration ((t-starts i)/durations i) = 0 := by
    have hdi := hd i (mem_range.mp hi)
    by_cases hij : i < j
    · apply SmoothStep.jets_after
      apply (le_div_iff₀ hdi).mpr
      linarith [hpast i hij]
    · apply SmoothStep.jets_before
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hfuture i hi (by omega))) hdi.le
  constructor
  · apply sum_eq_zero
    intro i hi
    simp only [SmoothStep.blendVelocity, (hz i hi).1, mul_zero, zero_div]
  · apply sum_eq_zero
    intro i hi
    simp only [SmoothStep.blendAcceleration, (hz i hi).2, mul_zero, zero_div]

end CoastInterpolation
end GNC.Planning
