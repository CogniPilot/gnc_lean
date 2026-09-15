import GNC.Control.Propellant

/-! Quantitative propellant comparisons using rational bounds on the actual
rocket-equation exponential. A delta-v percentage alone is not a propellant
percentage; these bounds provide a checked conversion with explicit exhaust
speed and impulse budgets. -/
noncomputable section
namespace GNC.Propellant

theorem fraction_bounds {z : ℝ} (hz : 0 ≤ z) :
    z/(1+z) ≤ 1-Real.exp (-z) ∧ 1-Real.exp (-z) ≤ z := by
  constructor
  · have hp : 0 < 1+z := by linarith
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp z) (Real.exp_pos (-z)).le
    rw [← Real.exp_add] at h
    simp only [add_neg_cancel, Real.exp_zero] at h
    nlinarith
  · linarith [Real.add_one_le_exp (-z)]

theorem consumed_bounds {mass exhaust J : ℝ} (hm : 0 ≤ mass)
    (he : 0 < exhaust) (hJ : 0 ≤ J) :
    mass*(J/(exhaust+J)) ≤ consumedMass mass exhaust J ∧
      consumedMass mass exhaust J ≤ mass*(J/exhaust) := by
  have h := fraction_bounds (div_nonneg hJ he.le)
  have hid : (J/exhaust)/(1+J/exhaust) = J/(exhaust+J) := by
    field_simp
  rw [hid] at h
  have hid' : consumedMass mass exhaust J = mass*(1-Real.exp (-(J/exhaust))) := by
    simp [consumedMass, remainingMass, neg_div, mul_sub]
  rw [hid']
  exact ⟨mul_le_mul_of_nonneg_left h.1 hm, mul_le_mul_of_nonneg_left h.2 hm⟩

theorem relative_saving_of_budget {mass exhaust J K lower ratio : ℝ}
    (hm : 0 < mass) (he : 0 < exhaust) (hJ : 0 ≤ J)
    (hl : 0 ≤ lower) (hK : lower ≤ K) (hr : 0 ≤ ratio)
    (hbudget : J/exhaust < ratio*(lower/(exhaust+lower))) :
    consumedMass mass exhaust J < ratio*consumedMass mass exhaust K := by
  have hu := (consumed_bounds hm.le he hJ).2
  have hlower := ((consumed_bounds hm.le he hl).1).trans (consumed_mono hm.le he hK)
  have hs := mul_lt_mul_of_pos_left hbudget hm
  have hrhs := mul_le_mul_of_nonneg_left hlower hr
  nlinarith

end GNC.Propellant
