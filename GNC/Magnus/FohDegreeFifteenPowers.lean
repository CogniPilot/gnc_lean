import GNC.Magnus.FohDegreeFifteenData

/-!
Kernel-checked convolutions for powers of the finite quaternion exponent.
-/

noncomputable section
open Matrix Polynomial
open scoped Quaternion Matrix
namespace GNC.Magnus
namespace DegreeFifteen
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem power_step_0 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 1 n = convolution f g z (powerData f g z 0) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_0, powerData_0_0, powerData_0_0_0, powerData_1, powerData_1_1, powerData_1_1_1, powerData_1_3, powerData_1_3_3, powerData_1_5, powerData_1_5_1, powerData_1_5_2, powerData_1_5_3, powerData_1_7, powerData_1_7_1, powerData_1_7_2, powerData_1_7_3, powerData_1_9, powerData_1_9_1, powerData_1_9_2, powerData_1_9_3, powerData_1_11, powerData_1_11_1, powerData_1_11_2, powerData_1_11_3, powerData_1_13, powerData_1_13_1, powerData_1_13_2, powerData_1_13_3, powerData_1_15, powerData_1_15_1, powerData_1_15_2, powerData_1_15_3, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_1 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 2 n = convolution f g z (powerData f g z 1) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_1, powerData_1_1, powerData_1_1_1, powerData_1_3, powerData_1_3_3, powerData_1_5, powerData_1_5_1, powerData_1_5_2, powerData_1_5_3, powerData_1_7, powerData_1_7_1, powerData_1_7_2, powerData_1_7_3, powerData_1_9, powerData_1_9_1, powerData_1_9_2, powerData_1_9_3, powerData_1_11, powerData_1_11_1, powerData_1_11_2, powerData_1_11_3, powerData_1_13, powerData_1_13_1, powerData_1_13_2, powerData_1_13_3, powerData_1_15, powerData_1_15_1, powerData_1_15_2, powerData_1_15_3, powerData_2, powerData_2_2, powerData_2_2_0, powerData_2_6, powerData_2_6_0, powerData_2_8, powerData_2_8_0, powerData_2_10, powerData_2_10_0, powerData_2_12, powerData_2_12_0, powerData_2_14, powerData_2_14_0, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_2 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 3 n = convolution f g z (powerData f g z 2) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_2, powerData_2_2, powerData_2_2_0, powerData_2_6, powerData_2_6_0, powerData_2_8, powerData_2_8_0, powerData_2_10, powerData_2_10_0, powerData_2_12, powerData_2_12_0, powerData_2_14, powerData_2_14_0, powerData_3, powerData_3_3, powerData_3_3_1, powerData_3_5, powerData_3_5_3, powerData_3_7, powerData_3_7_1, powerData_3_7_2, powerData_3_7_3, powerData_3_9, powerData_3_9_1, powerData_3_9_2, powerData_3_9_3, powerData_3_11, powerData_3_11_1, powerData_3_11_2, powerData_3_11_3, powerData_3_13, powerData_3_13_1, powerData_3_13_2, powerData_3_13_3, powerData_3_15, powerData_3_15_1, powerData_3_15_2, powerData_3_15_3, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_3 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 4 n = convolution f g z (powerData f g z 3) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_3, powerData_3_3, powerData_3_3_1, powerData_3_5, powerData_3_5_3, powerData_3_7, powerData_3_7_1, powerData_3_7_2, powerData_3_7_3, powerData_3_9, powerData_3_9_1, powerData_3_9_2, powerData_3_9_3, powerData_3_11, powerData_3_11_1, powerData_3_11_2, powerData_3_11_3, powerData_3_13, powerData_3_13_1, powerData_3_13_2, powerData_3_13_3, powerData_3_15, powerData_3_15_1, powerData_3_15_2, powerData_3_15_3, powerData_4, powerData_4_4, powerData_4_4_0, powerData_4_8, powerData_4_8_0, powerData_4_10, powerData_4_10_0, powerData_4_12, powerData_4_12_0, powerData_4_14, powerData_4_14_0, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_4 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 5 n = convolution f g z (powerData f g z 4) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_4, powerData_4_4, powerData_4_4_0, powerData_4_8, powerData_4_8_0, powerData_4_10, powerData_4_10_0, powerData_4_12, powerData_4_12_0, powerData_4_14, powerData_4_14_0, powerData_5, powerData_5_5, powerData_5_5_1, powerData_5_7, powerData_5_7_3, powerData_5_9, powerData_5_9_1, powerData_5_9_2, powerData_5_9_3, powerData_5_11, powerData_5_11_1, powerData_5_11_2, powerData_5_11_3, powerData_5_13, powerData_5_13_1, powerData_5_13_2, powerData_5_13_3, powerData_5_15, powerData_5_15_1, powerData_5_15_2, powerData_5_15_3, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_5 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 6 n = convolution f g z (powerData f g z 5) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_5, powerData_5_5, powerData_5_5_1, powerData_5_7, powerData_5_7_3, powerData_5_9, powerData_5_9_1, powerData_5_9_2, powerData_5_9_3, powerData_5_11, powerData_5_11_1, powerData_5_11_2, powerData_5_11_3, powerData_5_13, powerData_5_13_1, powerData_5_13_2, powerData_5_13_3, powerData_5_15, powerData_5_15_1, powerData_5_15_2, powerData_5_15_3, powerData_6, powerData_6_6, powerData_6_6_0, powerData_6_10, powerData_6_10_0, powerData_6_12, powerData_6_12_0, powerData_6_14, powerData_6_14_0, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_6 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 7 n = convolution f g z (powerData f g z 6) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_6, powerData_6_6, powerData_6_6_0, powerData_6_10, powerData_6_10_0, powerData_6_12, powerData_6_12_0, powerData_6_14, powerData_6_14_0, powerData_7, powerData_7_7, powerData_7_7_1, powerData_7_9, powerData_7_9_3, powerData_7_11, powerData_7_11_1, powerData_7_11_2, powerData_7_11_3, powerData_7_13, powerData_7_13_1, powerData_7_13_2, powerData_7_13_3, powerData_7_15, powerData_7_15_1, powerData_7_15_2, powerData_7_15_3, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_7 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 8 n = convolution f g z (powerData f g z 7) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_7, powerData_7_7, powerData_7_7_1, powerData_7_9, powerData_7_9_3, powerData_7_11, powerData_7_11_1, powerData_7_11_2, powerData_7_11_3, powerData_7_13, powerData_7_13_1, powerData_7_13_2, powerData_7_13_3, powerData_7_15, powerData_7_15_1, powerData_7_15_2, powerData_7_15_3, powerData_8, powerData_8_8, powerData_8_8_0, powerData_8_12, powerData_8_12_0, powerData_8_14, powerData_8_14_0, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_8 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 9 n = convolution f g z (powerData f g z 8) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_8, powerData_8_8, powerData_8_8_0, powerData_8_12, powerData_8_12_0, powerData_8_14, powerData_8_14_0, powerData_9, powerData_9_9, powerData_9_9_1, powerData_9_11, powerData_9_11_3, powerData_9_13, powerData_9_13_1, powerData_9_13_2, powerData_9_13_3, powerData_9_15, powerData_9_15_1, powerData_9_15_2, powerData_9_15_3, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_9 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 10 n = convolution f g z (powerData f g z 9) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_9, powerData_9_9, powerData_9_9_1, powerData_9_11, powerData_9_11_3, powerData_9_13, powerData_9_13_1, powerData_9_13_2, powerData_9_13_3, powerData_9_15, powerData_9_15_1, powerData_9_15_2, powerData_9_15_3, powerData_10, powerData_10_10, powerData_10_10_0, powerData_10_14, powerData_10_14_0, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_10 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 11 n = convolution f g z (powerData f g z 10) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_10, powerData_10_10, powerData_10_10_0, powerData_10_14, powerData_10_14_0, powerData_11, powerData_11_11, powerData_11_11_1, powerData_11_13, powerData_11_13_3, powerData_11_15, powerData_11_15_1, powerData_11_15_2, powerData_11_15_3, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_11 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 12 n = convolution f g z (powerData f g z 11) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_11, powerData_11_11, powerData_11_11_1, powerData_11_13, powerData_11_13_3, powerData_11_15, powerData_11_15_1, powerData_11_15_2, powerData_11_15_3, powerData_12, powerData_12_12, powerData_12_12_0, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_12 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 13 n = convolution f g z (powerData f g z 12) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_12, powerData_12_12, powerData_12_12_0, powerData_13, powerData_13_13, powerData_13_13_1, powerData_13_15, powerData_13_15_3, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_13 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 14 n = convolution f g z (powerData f g z 13) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_13, powerData_13_13, powerData_13_13_1, powerData_13_15, powerData_13_15_3, powerData_14, powerData_14_14, powerData_14_14_0, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring

theorem power_step_14 (f g z : ℝ) (n : ℕ) (hn : n < 16) :
    powerData f g z 15 n = convolution f g z (powerData f g z 14) (exponentData f g z) n := by
  interval_cases n <;> ext i <;> fin_cases i <;>
    simp only [convolution, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    simp [powerData, powerData_14, powerData_14_14, powerData_14_14_0, powerData_15, powerData_15_15, powerData_15_15_1, exponentData, exponentData_1, exponentData_1_1, exponentData_3, exponentData_3_3, exponentData_5, exponentData_5_1, exponentData_5_2, exponentData_5_3, exponentData_7, exponentData_7_1, exponentData_7_2, exponentData_7_3, exponentData_9, exponentData_9_1, exponentData_9_2, exponentData_9_3, exponentData_11, exponentData_11_1, exponentData_11_2, exponentData_11_3, exponentData_13, exponentData_13_1, exponentData_13_2, exponentData_13_3, exponentData_15, exponentData_15_1, exponentData_15_2, exponentData_15_3, product, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] <;> ring


end DegreeFifteen
end GNC.Magnus
