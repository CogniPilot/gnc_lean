import GNC.Applications.CertifiedBurn.Steps

/-! The velocity-row transition pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkMv_00 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 0 := by decide +kernel
theorem chkMv_01 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 1 := by decide +kernel
theorem chkMv_02 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 2 := by decide +kernel
theorem chkMv_03 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 3 := by decide +kernel
theorem chkMv_04 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 4 := by decide +kernel
theorem chkMv_05 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 5 := by decide +kernel
theorem chkMv_06 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 6 := by decide +kernel
theorem chkMv_07 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 7 := by decide +kernel
theorem chkMv_08 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 8 := by decide +kernel
theorem chkMv_09 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 9 := by decide +kernel
theorem chkMv_10 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 10 := by decide +kernel
theorem chkMv_11 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 11 := by decide +kernel
theorem chkMv_12 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 12 := by decide +kernel
theorem chkMv_13 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 13 := by decide +kernel
theorem chkMv_14 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 14 := by decide +kernel
theorem chkMv_15 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 15 := by decide +kernel
theorem chkMv_16 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 16 := by decide +kernel
theorem chkMv_17 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 17 := by decide +kernel
theorem chkMv_18 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 18 := by decide +kernel
theorem chkMv_19 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 19 := by decide +kernel
theorem chkMv_20 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 20 := by decide +kernel
theorem chkMv_21 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 21 := by decide +kernel
theorem chkMv_22 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 22 := by decide +kernel
theorem chkMv_23 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 23 := by decide +kernel
theorem chkMv_24 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 24 := by decide +kernel
theorem chkMv_25 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 25 := by decide +kernel
theorem chkMv_26 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 26 := by decide +kernel
theorem chkMv_27 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 27 := by decide +kernel
theorem chkMv_28 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 28 := by decide +kernel
theorem chkMv_29 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 29 := by decide +kernel
theorem chkMv_30 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 30 := by decide +kernel
theorem chkMv_31 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 31 := by decide +kernel
theorem chkMv_32 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 32 := by decide +kernel
theorem chkMv_33 : pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) 33 := by decide +kernel

theorem chkMv : ∀ i, i ≤ 33 → pairChecksM steps {2, 3} (fun r => r.kMv) (fun r => r.kSv) i
  | 0, _ => chkMv_00
  | 1, _ => chkMv_01
  | 2, _ => chkMv_02
  | 3, _ => chkMv_03
  | 4, _ => chkMv_04
  | 5, _ => chkMv_05
  | 6, _ => chkMv_06
  | 7, _ => chkMv_07
  | 8, _ => chkMv_08
  | 9, _ => chkMv_09
  | 10, _ => chkMv_10
  | 11, _ => chkMv_11
  | 12, _ => chkMv_12
  | 13, _ => chkMv_13
  | 14, _ => chkMv_14
  | 15, _ => chkMv_15
  | 16, _ => chkMv_16
  | 17, _ => chkMv_17
  | 18, _ => chkMv_18
  | 19, _ => chkMv_19
  | 20, _ => chkMv_20
  | 21, _ => chkMv_21
  | 22, _ => chkMv_22
  | 23, _ => chkMv_23
  | 24, _ => chkMv_24
  | 25, _ => chkMv_25
  | 26, _ => chkMv_26
  | 27, _ => chkMv_27
  | 28, _ => chkMv_28
  | 29, _ => chkMv_29
  | 30, _ => chkMv_30
  | 31, _ => chkMv_31
  | 32, _ => chkMv_32
  | 33, _ => chkMv_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
