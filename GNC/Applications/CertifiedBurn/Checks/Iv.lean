import GNC.Applications.CertifiedBurn.Steps

/-! The velocity-row initial column-split pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkIv_00 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 0 := by decide +kernel
theorem chkIv_01 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 1 := by decide +kernel
theorem chkIv_02 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 2 := by decide +kernel
theorem chkIv_03 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 3 := by decide +kernel
theorem chkIv_04 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 4 := by decide +kernel
theorem chkIv_05 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 5 := by decide +kernel
theorem chkIv_06 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 6 := by decide +kernel
theorem chkIv_07 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 7 := by decide +kernel
theorem chkIv_08 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 8 := by decide +kernel
theorem chkIv_09 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 9 := by decide +kernel
theorem chkIv_10 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 10 := by decide +kernel
theorem chkIv_11 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 11 := by decide +kernel
theorem chkIv_12 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 12 := by decide +kernel
theorem chkIv_13 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 13 := by decide +kernel
theorem chkIv_14 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 14 := by decide +kernel
theorem chkIv_15 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 15 := by decide +kernel
theorem chkIv_16 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 16 := by decide +kernel
theorem chkIv_17 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 17 := by decide +kernel
theorem chkIv_18 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 18 := by decide +kernel
theorem chkIv_19 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 19 := by decide +kernel
theorem chkIv_20 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 20 := by decide +kernel
theorem chkIv_21 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 21 := by decide +kernel
theorem chkIv_22 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 22 := by decide +kernel
theorem chkIv_23 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 23 := by decide +kernel
theorem chkIv_24 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 24 := by decide +kernel
theorem chkIv_25 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 25 := by decide +kernel
theorem chkIv_26 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 26 := by decide +kernel
theorem chkIv_27 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 27 := by decide +kernel
theorem chkIv_28 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 28 := by decide +kernel
theorem chkIv_29 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 29 := by decide +kernel
theorem chkIv_30 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 30 := by decide +kernel
theorem chkIv_31 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 31 := by decide +kernel
theorem chkIv_32 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 32 := by decide +kernel
theorem chkIv_33 : initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) 33 := by decide +kernel

theorem chkIv : ∀ i, i ≤ 33 → initChecks steps {2, 3} (fun r => r.kMv0p) (fun r => r.kMv0v) i
  | 0, _ => chkIv_00
  | 1, _ => chkIv_01
  | 2, _ => chkIv_02
  | 3, _ => chkIv_03
  | 4, _ => chkIv_04
  | 5, _ => chkIv_05
  | 6, _ => chkIv_06
  | 7, _ => chkIv_07
  | 8, _ => chkIv_08
  | 9, _ => chkIv_09
  | 10, _ => chkIv_10
  | 11, _ => chkIv_11
  | 12, _ => chkIv_12
  | 13, _ => chkIv_13
  | 14, _ => chkIv_14
  | 15, _ => chkIv_15
  | 16, _ => chkIv_16
  | 17, _ => chkIv_17
  | 18, _ => chkIv_18
  | 19, _ => chkIv_19
  | 20, _ => chkIv_20
  | 21, _ => chkIv_21
  | 22, _ => chkIv_22
  | 23, _ => chkIv_23
  | 24, _ => chkIv_24
  | 25, _ => chkIv_25
  | 26, _ => chkIv_26
  | 27, _ => chkIv_27
  | 28, _ => chkIv_28
  | 29, _ => chkIv_29
  | 30, _ => chkIv_30
  | 31, _ => chkIv_31
  | 32, _ => chkIv_32
  | 33, _ => chkIv_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
