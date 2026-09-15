import GNC.Control.ThrustSupport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Exact angular-cap to acceleration-error conversion. -/
noncomputable section
open Matrix Real
namespace GNC.ThrustSupport

/-- A physical unit-direction cap gives the exact chord-radius envelope. -/
theorem cap_angle_distance (n q : Vec3) {α : ℝ} (hn : n ⬝ᵥ n = 1)
    (hq : q ∈ Cap n (cos α)) (hα : 0 ≤ α) (hπ : α ≤ π) :
    enorm (q-n) ≤ 2*sin (α/2) := by
  have hs : 0 ≤ sin (α/2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  apply cap_in_chord_ball n q (cos α) (2*sin (α/2)) hn hq (by positivity)
  have hc := cos_two_mul (α/2)
  have hsc := sin_sq_add_cos_sq (α/2)
  have hdouble : 2*(α/2) = α := by ring
  rw [hdouble] at hc
  nlinarith

/-- Acceleration magnitude and pointing uncertainty stay separate. -/
theorem acceleration_angle_error (n q : Vec3) {α a : ℝ} (hn : n ⬝ᵥ n = 1)
    (hq : q ∈ Cap n (cos α)) (hα : 0 ≤ α) (hπ : α ≤ π) (ha : 0 ≤ a) :
    enorm (a • (q-n)) ≤ 2*a*sin (α/2) := by
  rw [enorm_smul, abs_of_nonneg ha]
  convert mul_le_mul_of_nonneg_left (cap_angle_distance n q hn hq hα hπ) ha using 1
  ring

end GNC.ThrustSupport
