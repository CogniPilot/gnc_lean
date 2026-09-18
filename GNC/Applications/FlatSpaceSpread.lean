import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! The flat-space disturbance-spread estimate behind the chemical-burn
"small factor" remark, with the rounded burn/coast durations of the motor
section. The worst case combines a constant admitted disturbance over the
burn with coast drift and the three-component factor. -/
noncomputable section
namespace GNC.FlatSpaceSpread
open Set

/-- Disturbance bound per component (m/s^2): (F_B/m_i)*(6/5)/100. -/
def d : ℝ := 31/2500
/-- Burn duration (s), the rounded t_*/5. -/
def Tb : ℝ := 371/2
/-- Coast duration (s), the rounded 2t_*/5. -/
def Tc : ℝ := 3711/10

/-- Worst-case three-component position spread in flat space (m). -/
def spreadP : ℝ := Real.sqrt 3 * (d * (Tb^2/2 + Tb*Tc))
/-- Worst-case three-component velocity spread in flat space (m/s). -/
def spreadV : ℝ := Real.sqrt 3 * (d * Tb)

theorem sqrt3_bounds : (1732/1000 : ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 17321/10000 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The flat-space position spread is about 1.8 km. -/
theorem spreadP_bounds : spreadP ∈ Icc (1847 : ℝ) 1849 := by
  obtain ⟨hlo, hhi⟩ := sqrt3_bounds
  have hC : d * (Tb^2/2 + Tb*Tc) = 106694777/100000 := by
    unfold d Tb Tc; norm_num
  have hC0 : (0:ℝ) ≤ 106694777/100000 := by norm_num
  unfold spreadP
  rw [hC]
  constructor
  · calc (1847:ℝ) ≤ (1732/1000) * (106694777/100000) := by norm_num
    _ ≤ Real.sqrt 3 * (106694777/100000) :=
        mul_le_mul_of_nonneg_right hlo hC0
  · calc Real.sqrt 3 * (106694777/100000)
        ≤ (17321/10000) * (106694777/100000) :=
        mul_le_mul_of_nonneg_right hhi hC0
    _ ≤ 1849 := by norm_num

/-- The flat-space velocity spread is about 4 m/s. -/
theorem spreadV_bounds : spreadV ∈ Icc (398/100 : ℝ) (399/100) := by
  obtain ⟨hlo, hhi⟩ := sqrt3_bounds
  have hC : d * Tb = 11501/5000 := by unfold d Tb; norm_num
  have hC0 : (0:ℝ) ≤ 11501/5000 := by norm_num
  unfold spreadV
  rw [hC]
  constructor
  · calc (398/100 : ℝ) ≤ (1732/1000) * (11501/5000) := by norm_num
    _ ≤ Real.sqrt 3 * (11501/5000) := mul_le_mul_of_nonneg_right hlo hC0
  · calc Real.sqrt 3 * (11501/5000) ≤ (17321/10000) * (11501/5000) :=
        mul_le_mul_of_nonneg_right hhi hC0
    _ ≤ 399/100 := by norm_num

end GNC.FlatSpaceSpread
