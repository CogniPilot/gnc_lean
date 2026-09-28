import GNC.Applications.CertifiedBurn.Steps

/-! The position-row velocity-column kernel pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkVp_00 : pairChecksV steps {0, 1} (fun r => r.kVp) 0 := by decide +kernel
theorem chkVp_01 : pairChecksV steps {0, 1} (fun r => r.kVp) 1 := by decide +kernel
theorem chkVp_02 : pairChecksV steps {0, 1} (fun r => r.kVp) 2 := by decide +kernel
theorem chkVp_03 : pairChecksV steps {0, 1} (fun r => r.kVp) 3 := by decide +kernel
theorem chkVp_04 : pairChecksV steps {0, 1} (fun r => r.kVp) 4 := by decide +kernel
theorem chkVp_05 : pairChecksV steps {0, 1} (fun r => r.kVp) 5 := by decide +kernel
theorem chkVp_06 : pairChecksV steps {0, 1} (fun r => r.kVp) 6 := by decide +kernel
theorem chkVp_07 : pairChecksV steps {0, 1} (fun r => r.kVp) 7 := by decide +kernel
theorem chkVp_08 : pairChecksV steps {0, 1} (fun r => r.kVp) 8 := by decide +kernel
theorem chkVp_09 : pairChecksV steps {0, 1} (fun r => r.kVp) 9 := by decide +kernel
theorem chkVp_10 : pairChecksV steps {0, 1} (fun r => r.kVp) 10 := by decide +kernel
theorem chkVp_11 : pairChecksV steps {0, 1} (fun r => r.kVp) 11 := by decide +kernel
theorem chkVp_12 : pairChecksV steps {0, 1} (fun r => r.kVp) 12 := by decide +kernel
theorem chkVp_13 : pairChecksV steps {0, 1} (fun r => r.kVp) 13 := by decide +kernel
theorem chkVp_14 : pairChecksV steps {0, 1} (fun r => r.kVp) 14 := by decide +kernel
theorem chkVp_15 : pairChecksV steps {0, 1} (fun r => r.kVp) 15 := by decide +kernel
theorem chkVp_16 : pairChecksV steps {0, 1} (fun r => r.kVp) 16 := by decide +kernel
theorem chkVp_17 : pairChecksV steps {0, 1} (fun r => r.kVp) 17 := by decide +kernel
theorem chkVp_18 : pairChecksV steps {0, 1} (fun r => r.kVp) 18 := by decide +kernel
theorem chkVp_19 : pairChecksV steps {0, 1} (fun r => r.kVp) 19 := by decide +kernel
theorem chkVp_20 : pairChecksV steps {0, 1} (fun r => r.kVp) 20 := by decide +kernel
theorem chkVp_21 : pairChecksV steps {0, 1} (fun r => r.kVp) 21 := by decide +kernel
theorem chkVp_22 : pairChecksV steps {0, 1} (fun r => r.kVp) 22 := by decide +kernel
theorem chkVp_23 : pairChecksV steps {0, 1} (fun r => r.kVp) 23 := by decide +kernel
theorem chkVp_24 : pairChecksV steps {0, 1} (fun r => r.kVp) 24 := by decide +kernel
theorem chkVp_25 : pairChecksV steps {0, 1} (fun r => r.kVp) 25 := by decide +kernel
theorem chkVp_26 : pairChecksV steps {0, 1} (fun r => r.kVp) 26 := by decide +kernel
theorem chkVp_27 : pairChecksV steps {0, 1} (fun r => r.kVp) 27 := by decide +kernel
theorem chkVp_28 : pairChecksV steps {0, 1} (fun r => r.kVp) 28 := by decide +kernel
theorem chkVp_29 : pairChecksV steps {0, 1} (fun r => r.kVp) 29 := by decide +kernel
theorem chkVp_30 : pairChecksV steps {0, 1} (fun r => r.kVp) 30 := by decide +kernel
theorem chkVp_31 : pairChecksV steps {0, 1} (fun r => r.kVp) 31 := by decide +kernel
theorem chkVp_32 : pairChecksV steps {0, 1} (fun r => r.kVp) 32 := by decide +kernel
theorem chkVp_33 : pairChecksV steps {0, 1} (fun r => r.kVp) 33 := by decide +kernel

theorem chkVp : ∀ i, i ≤ 33 → pairChecksV steps {0, 1} (fun r => r.kVp) i
  | 0, _ => chkVp_00
  | 1, _ => chkVp_01
  | 2, _ => chkVp_02
  | 3, _ => chkVp_03
  | 4, _ => chkVp_04
  | 5, _ => chkVp_05
  | 6, _ => chkVp_06
  | 7, _ => chkVp_07
  | 8, _ => chkVp_08
  | 9, _ => chkVp_09
  | 10, _ => chkVp_10
  | 11, _ => chkVp_11
  | 12, _ => chkVp_12
  | 13, _ => chkVp_13
  | 14, _ => chkVp_14
  | 15, _ => chkVp_15
  | 16, _ => chkVp_16
  | 17, _ => chkVp_17
  | 18, _ => chkVp_18
  | 19, _ => chkVp_19
  | 20, _ => chkVp_20
  | 21, _ => chkVp_21
  | 22, _ => chkVp_22
  | 23, _ => chkVp_23
  | 24, _ => chkVp_24
  | 25, _ => chkVp_25
  | 26, _ => chkVp_26
  | 27, _ => chkVp_27
  | 28, _ => chkVp_28
  | 29, _ => chkVp_29
  | 30, _ => chkVp_30
  | 31, _ => chkVp_31
  | 32, _ => chkVp_32
  | 33, _ => chkVp_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
