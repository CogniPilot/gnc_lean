import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! A formal correction to Remark 6: the HCW pv block has singularities away
from integer multiples of π. Everything here concerns the exact real matrix.
-/
noncomputable section
open Real Set Matrix
namespace GNC.SingularTimes

def inPlaneDet (t : ℝ) := 8 - 8*cos t - 3*t*sin t

/-- Equation (91), in normalized units n=1. -/
def pv (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sin t, 2*(1-cos t), 0; -2*(1-cos t), 4*sin t-3*t, 0; 0, 0, sin t]

theorem det_pv (t : ℝ) : (pv t).det = sin t * inPlaneDet t := by
  simp [pv, Matrix.det_fin_three, inPlaneDet]
  linear_combination 4 * sin t * (sin_sq_add_cos_sq t)

/-- Both factors, not just sin(t), contribute singular horizons. -/
theorem singular_iff (t : ℝ) :
    (pv t).det = 0 ↔ sin t = 0 ∨ inPlaneDet t = 0 := by
  rw [det_pv, mul_eq_zero]

theorem left_sign : inPlaneDet (5*π/2) < 0 := by
  have he : 5*π/2 = π/2 + 2*π := by ring
  simp [inPlaneDet, he]
  linarith [Real.two_le_pi]

theorem right_sign : 0 < inPlaneDet (3*π) := by
  have he : 3*π = π + 2*π := by ring
  simp [inPlaneDet, he]

/-- A singular horizon strictly between 5π/2 and 3π, with nonzero sin(t).
Thus it cannot be an integer half-orbit. -/
theorem exists_additional_singularity :
    ∃ t : ℝ, 5*π/2 < t ∧ t < 3*π ∧ (pv t).det = 0 ∧ sin t ≠ 0 := by
  have hab : 5*π/2 ≤ 3*π := by linarith [pi_pos]
  have hc : Continuous inPlaneDet := by unfold inPlaneDet; fun_prop
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc hab hc.continuousOn
    (show (0 : ℝ) ∈ Icc (inPlaneDet (5*π/2)) (inPlaneDet (3*π)) from
      ⟨left_sign.le, right_sign.le⟩)
  have hlo : 5*π/2 < t := lt_of_le_of_ne ht.1 (by
    intro he; have := left_sign; rw [he, hz] at this; exact (lt_irrefl _ this))
  have hhi : t < 3*π := lt_of_le_of_ne ht.2 (by
    intro he; have := right_sign; rw [← he, hz] at this; exact (lt_irrefl _ this))
  refine ⟨t, hlo, hhi, ?_, ?_⟩
  · rw [det_pv, hz, mul_zero]
  · have hs : 0 < sin (t - 2*π) :=
      sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) (by linarith)
    rw [sin_sub_two_pi] at hs
    exact hs.ne'

/-- Direct negation of the claimed exhaustive integer-half-orbit condition. -/
theorem exists_non_half_orbit_singular_time :
    ∃ t : ℝ, 0 < t ∧ (pv t).det = 0 ∧ ∀ k : ℤ, t ≠ (k : ℝ)*π := by
  obtain ⟨t, hlo, _, hdet, hs⟩ := exists_additional_singularity
  refine ⟨t, by linarith [pi_pos], hdet, ?_⟩
  intro k hk
  apply hs
  rw [hk, sin_int_mul_pi]

end GNC.SingularTimes
