import GNC.Applications.Backstepping.FixedWingReference
import GNC.Applications.Backstepping.FixedWingAllocation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Continuous-time force-feasibility certificate for the numerical example.
No sampled maximum or floating-point evaluation is used in these proofs.
-/
noncomputable section
open Real Set
namespace GNC.FixedWingExample

def speed (yd : ℝ) : ℝ := sqrt (25^2+yd^2)
def tangentialAcceleration (yd ydd : ℝ) : ℝ := yd*ydd/speed yd
def normalAcceleration (yd ydd : ℝ) : ℝ := 25*ydd/speed yd
def liftSlope (yd : ℝ) : ℝ := (49/32:ℝ)*(speed yd)^2
def tangentialForce (yd ydd : ℝ) : ℝ :=
  (147/16000:ℝ)*(speed yd)^2+2*tangentialAcceleration yd ydd
def normalLoad (yd ydd : ℝ) : ℝ :=
  2*sqrt ((981/100:ℝ)^2+(normalAcceleration yd ydd)^2)

theorem speed_lower (yd : ℝ) : 25 ≤ speed yd := by
  have hs := sq_sqrt (by positivity : (0:ℝ) ≤ 25^2+yd^2)
  have hn := sqrt_nonneg (25^2+yd^2)
  dsimp [speed]
  nlinarith [sq_nonneg yd]

theorem acceleration_bounds {yd ydd : ℝ}
    (hv : |yd| ≤ 175/24) (ha : |ydd| ≤ 35/12) :
    |tangentialAcceleration yd ydd| < 1 ∧ |normalAcceleration yd ydd| < 3 := by
  have hs := speed_lower yd
  have hsp : 0 < speed yd := by linarith
  have hm := mul_le_mul hv ha (abs_nonneg ydd) (by norm_num : (0:ℝ) ≤ 175/24)
  constructor
  · rw [tangentialAcceleration, abs_div, abs_mul, abs_of_pos hsp, div_lt_iff₀ hsp]
    nlinarith
  · rw [normalAcceleration, abs_div, abs_mul, abs_of_pos hsp, div_lt_iff₀ hsp]
    norm_num
    nlinarith

theorem force_branch_conditions {yd ydd : ℝ}
    (hv : |yd| ≤ 175/24) (ha : |ydd| ≤ 35/12) :
    0 < liftSlope yd ∧ 0 < tangentialForce yd ydd ∧
    0 < normalLoad yd ydd ∧ normalLoad yd ydd ≤ liftSlope yd*(1/10:ℝ) := by
  have hs := speed_lower yd
  obtain ⟨hat, han⟩ := acceleration_bounds hv ha
  have hat' := (abs_lt.mp hat).1
  have han' := abs_lt.mp han
  have hroot := sq_sqrt (by positivity :
    (0:ℝ) ≤ (981/100:ℝ)^2+(normalAcceleration yd ydd)^2)
  have hn := sqrt_nonneg ((981/100:ℝ)^2+(normalAcceleration yd ydd)^2)
  have hnp : 0 < sqrt ((981/100:ℝ)^2+(normalAcceleration yd ydd)^2) := by positivity
  have hload : normalLoad yd ydd ≤ 21 := by
    dsimp [normalLoad]
    nlinarith
  dsimp [liftSlope, tangentialForce, normalLoad] at *
  refine ⟨by positivity, ?_, by positivity, ?_⟩ <;> nlinarith

/-- Every time in the maneuver admits one and only one angle in [0, 0.1].
Together with force_balance and bank_balance this certifies the ideal force
allocation continuously over the arc, including both endpoints. -/
theorem reference_force_feasible {t : ℝ} (ht : t ∈ Icc 0 30) :
    let yd := FixedWingReference.lateralVelocity 100 30 t
    let ydd := FixedWingReference.lateralAcceleration 100 30 t
    ∃! α : ℝ, α ∈ Icc 0 (1/10:ℝ) ∧
      FixedWingAllocation.liftEquation (liftSlope yd) (tangentialForce yd ydd) α =
        normalLoad yd ydd := by
  dsimp
  obtain ⟨hv, ha⟩ := FixedWingReference.example_derivative_bounds ht
  obtain ⟨hK,hA,hL,hload⟩ := force_branch_conditions hv ha
  exact FixedWingAllocation.exists_unique_angle hK hA.le hL (by norm_num)
    (by linarith [Real.two_le_pi]) hload

end GNC.FixedWingExample
