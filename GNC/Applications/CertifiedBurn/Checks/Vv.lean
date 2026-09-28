import GNC.Applications.CertifiedBurn.Steps

/-! The velocity-row velocity-column kernel pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkVv_00 : pairChecksV steps {2, 3} (fun r => r.kVv) 0 := by decide +kernel
theorem chkVv_01 : pairChecksV steps {2, 3} (fun r => r.kVv) 1 := by decide +kernel
theorem chkVv_02 : pairChecksV steps {2, 3} (fun r => r.kVv) 2 := by decide +kernel
theorem chkVv_03 : pairChecksV steps {2, 3} (fun r => r.kVv) 3 := by decide +kernel
theorem chkVv_04 : pairChecksV steps {2, 3} (fun r => r.kVv) 4 := by decide +kernel
theorem chkVv_05 : pairChecksV steps {2, 3} (fun r => r.kVv) 5 := by decide +kernel
theorem chkVv_06 : pairChecksV steps {2, 3} (fun r => r.kVv) 6 := by decide +kernel
theorem chkVv_07 : pairChecksV steps {2, 3} (fun r => r.kVv) 7 := by decide +kernel
theorem chkVv_08 : pairChecksV steps {2, 3} (fun r => r.kVv) 8 := by decide +kernel
theorem chkVv_09 : pairChecksV steps {2, 3} (fun r => r.kVv) 9 := by decide +kernel
theorem chkVv_10 : pairChecksV steps {2, 3} (fun r => r.kVv) 10 := by decide +kernel
theorem chkVv_11 : pairChecksV steps {2, 3} (fun r => r.kVv) 11 := by decide +kernel
theorem chkVv_12 : pairChecksV steps {2, 3} (fun r => r.kVv) 12 := by decide +kernel
theorem chkVv_13 : pairChecksV steps {2, 3} (fun r => r.kVv) 13 := by decide +kernel
theorem chkVv_14 : pairChecksV steps {2, 3} (fun r => r.kVv) 14 := by decide +kernel
theorem chkVv_15 : pairChecksV steps {2, 3} (fun r => r.kVv) 15 := by decide +kernel
theorem chkVv_16 : pairChecksV steps {2, 3} (fun r => r.kVv) 16 := by decide +kernel
theorem chkVv_17 : pairChecksV steps {2, 3} (fun r => r.kVv) 17 := by decide +kernel
theorem chkVv_18 : pairChecksV steps {2, 3} (fun r => r.kVv) 18 := by decide +kernel
theorem chkVv_19 : pairChecksV steps {2, 3} (fun r => r.kVv) 19 := by decide +kernel
theorem chkVv_20 : pairChecksV steps {2, 3} (fun r => r.kVv) 20 := by decide +kernel
theorem chkVv_21 : pairChecksV steps {2, 3} (fun r => r.kVv) 21 := by decide +kernel
theorem chkVv_22 : pairChecksV steps {2, 3} (fun r => r.kVv) 22 := by decide +kernel
theorem chkVv_23 : pairChecksV steps {2, 3} (fun r => r.kVv) 23 := by decide +kernel
theorem chkVv_24 : pairChecksV steps {2, 3} (fun r => r.kVv) 24 := by decide +kernel
theorem chkVv_25 : pairChecksV steps {2, 3} (fun r => r.kVv) 25 := by decide +kernel
theorem chkVv_26 : pairChecksV steps {2, 3} (fun r => r.kVv) 26 := by decide +kernel
theorem chkVv_27 : pairChecksV steps {2, 3} (fun r => r.kVv) 27 := by decide +kernel
theorem chkVv_28 : pairChecksV steps {2, 3} (fun r => r.kVv) 28 := by decide +kernel
theorem chkVv_29 : pairChecksV steps {2, 3} (fun r => r.kVv) 29 := by decide +kernel
theorem chkVv_30 : pairChecksV steps {2, 3} (fun r => r.kVv) 30 := by decide +kernel
theorem chkVv_31 : pairChecksV steps {2, 3} (fun r => r.kVv) 31 := by decide +kernel
theorem chkVv_32 : pairChecksV steps {2, 3} (fun r => r.kVv) 32 := by decide +kernel
theorem chkVv_33 : pairChecksV steps {2, 3} (fun r => r.kVv) 33 := by decide +kernel

theorem chkVv : ∀ i, i ≤ 33 → pairChecksV steps {2, 3} (fun r => r.kVv) i
  | 0, _ => chkVv_00
  | 1, _ => chkVv_01
  | 2, _ => chkVv_02
  | 3, _ => chkVv_03
  | 4, _ => chkVv_04
  | 5, _ => chkVv_05
  | 6, _ => chkVv_06
  | 7, _ => chkVv_07
  | 8, _ => chkVv_08
  | 9, _ => chkVv_09
  | 10, _ => chkVv_10
  | 11, _ => chkVv_11
  | 12, _ => chkVv_12
  | 13, _ => chkVv_13
  | 14, _ => chkVv_14
  | 15, _ => chkVv_15
  | 16, _ => chkVv_16
  | 17, _ => chkVv_17
  | 18, _ => chkVv_18
  | 19, _ => chkVv_19
  | 20, _ => chkVv_20
  | 21, _ => chkVv_21
  | 22, _ => chkVv_22
  | 23, _ => chkVv_23
  | 24, _ => chkVv_24
  | 25, _ => chkVv_25
  | 26, _ => chkVv_26
  | 27, _ => chkVv_27
  | 28, _ => chkVv_28
  | 29, _ => chkVv_29
  | 30, _ => chkVv_30
  | 31, _ => chkVv_31
  | 32, _ => chkVv_32
  | 33, _ => chkVv_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
