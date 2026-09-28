import GNC.Applications.CertifiedBurn.Steps

/-! The position-row initial column-split pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkIp_00 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 0 := by decide +kernel
theorem chkIp_01 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 1 := by decide +kernel
theorem chkIp_02 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 2 := by decide +kernel
theorem chkIp_03 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 3 := by decide +kernel
theorem chkIp_04 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 4 := by decide +kernel
theorem chkIp_05 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 5 := by decide +kernel
theorem chkIp_06 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 6 := by decide +kernel
theorem chkIp_07 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 7 := by decide +kernel
theorem chkIp_08 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 8 := by decide +kernel
theorem chkIp_09 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 9 := by decide +kernel
theorem chkIp_10 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 10 := by decide +kernel
theorem chkIp_11 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 11 := by decide +kernel
theorem chkIp_12 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 12 := by decide +kernel
theorem chkIp_13 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 13 := by decide +kernel
theorem chkIp_14 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 14 := by decide +kernel
theorem chkIp_15 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 15 := by decide +kernel
theorem chkIp_16 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 16 := by decide +kernel
theorem chkIp_17 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 17 := by decide +kernel
theorem chkIp_18 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 18 := by decide +kernel
theorem chkIp_19 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 19 := by decide +kernel
theorem chkIp_20 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 20 := by decide +kernel
theorem chkIp_21 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 21 := by decide +kernel
theorem chkIp_22 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 22 := by decide +kernel
theorem chkIp_23 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 23 := by decide +kernel
theorem chkIp_24 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 24 := by decide +kernel
theorem chkIp_25 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 25 := by decide +kernel
theorem chkIp_26 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 26 := by decide +kernel
theorem chkIp_27 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 27 := by decide +kernel
theorem chkIp_28 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 28 := by decide +kernel
theorem chkIp_29 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 29 := by decide +kernel
theorem chkIp_30 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 30 := by decide +kernel
theorem chkIp_31 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 31 := by decide +kernel
theorem chkIp_32 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 32 := by decide +kernel
theorem chkIp_33 : initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) 33 := by decide +kernel

theorem chkIp : ∀ i, i ≤ 33 → initChecks steps {0, 1} (fun r => r.kMp0p) (fun r => r.kMp0v) i
  | 0, _ => chkIp_00
  | 1, _ => chkIp_01
  | 2, _ => chkIp_02
  | 3, _ => chkIp_03
  | 4, _ => chkIp_04
  | 5, _ => chkIp_05
  | 6, _ => chkIp_06
  | 7, _ => chkIp_07
  | 8, _ => chkIp_08
  | 9, _ => chkIp_09
  | 10, _ => chkIp_10
  | 11, _ => chkIp_11
  | 12, _ => chkIp_12
  | 13, _ => chkIp_13
  | 14, _ => chkIp_14
  | 15, _ => chkIp_15
  | 16, _ => chkIp_16
  | 17, _ => chkIp_17
  | 18, _ => chkIp_18
  | 19, _ => chkIp_19
  | 20, _ => chkIp_20
  | 21, _ => chkIp_21
  | 22, _ => chkIp_22
  | 23, _ => chkIp_23
  | 24, _ => chkIp_24
  | 25, _ => chkIp_25
  | 26, _ => chkIp_26
  | 27, _ => chkIp_27
  | 28, _ => chkIp_28
  | 29, _ => chkIp_29
  | 30, _ => chkIp_30
  | 31, _ => chkIp_31
  | 32, _ => chkIp_32
  | 33, _ => chkIp_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
