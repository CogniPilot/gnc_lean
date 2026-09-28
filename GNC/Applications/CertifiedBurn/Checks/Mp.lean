import GNC.Applications.CertifiedBurn.Steps

/-! The position-row transition pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkMp_00 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 0 := by decide +kernel
theorem chkMp_01 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 1 := by decide +kernel
theorem chkMp_02 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 2 := by decide +kernel
theorem chkMp_03 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 3 := by decide +kernel
theorem chkMp_04 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 4 := by decide +kernel
theorem chkMp_05 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 5 := by decide +kernel
theorem chkMp_06 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 6 := by decide +kernel
theorem chkMp_07 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 7 := by decide +kernel
theorem chkMp_08 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 8 := by decide +kernel
theorem chkMp_09 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 9 := by decide +kernel
theorem chkMp_10 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 10 := by decide +kernel
theorem chkMp_11 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 11 := by decide +kernel
theorem chkMp_12 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 12 := by decide +kernel
theorem chkMp_13 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 13 := by decide +kernel
theorem chkMp_14 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 14 := by decide +kernel
theorem chkMp_15 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 15 := by decide +kernel
theorem chkMp_16 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 16 := by decide +kernel
theorem chkMp_17 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 17 := by decide +kernel
theorem chkMp_18 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 18 := by decide +kernel
theorem chkMp_19 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 19 := by decide +kernel
theorem chkMp_20 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 20 := by decide +kernel
theorem chkMp_21 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 21 := by decide +kernel
theorem chkMp_22 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 22 := by decide +kernel
theorem chkMp_23 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 23 := by decide +kernel
theorem chkMp_24 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 24 := by decide +kernel
theorem chkMp_25 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 25 := by decide +kernel
theorem chkMp_26 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 26 := by decide +kernel
theorem chkMp_27 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 27 := by decide +kernel
theorem chkMp_28 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 28 := by decide +kernel
theorem chkMp_29 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 29 := by decide +kernel
theorem chkMp_30 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 30 := by decide +kernel
theorem chkMp_31 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 31 := by decide +kernel
theorem chkMp_32 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 32 := by decide +kernel
theorem chkMp_33 : pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) 33 := by decide +kernel

theorem chkMp : ∀ i, i ≤ 33 → pairChecksM steps {0, 1} (fun r => r.kMp) (fun r => r.kSp) i
  | 0, _ => chkMp_00
  | 1, _ => chkMp_01
  | 2, _ => chkMp_02
  | 3, _ => chkMp_03
  | 4, _ => chkMp_04
  | 5, _ => chkMp_05
  | 6, _ => chkMp_06
  | 7, _ => chkMp_07
  | 8, _ => chkMp_08
  | 9, _ => chkMp_09
  | 10, _ => chkMp_10
  | 11, _ => chkMp_11
  | 12, _ => chkMp_12
  | 13, _ => chkMp_13
  | 14, _ => chkMp_14
  | 15, _ => chkMp_15
  | 16, _ => chkMp_16
  | 17, _ => chkMp_17
  | 18, _ => chkMp_18
  | 19, _ => chkMp_19
  | 20, _ => chkMp_20
  | 21, _ => chkMp_21
  | 22, _ => chkMp_22
  | 23, _ => chkMp_23
  | 24, _ => chkMp_24
  | 25, _ => chkMp_25
  | 26, _ => chkMp_26
  | 27, _ => chkMp_27
  | 28, _ => chkMp_28
  | 29, _ => chkMp_29
  | 30, _ => chkMp_30
  | 31, _ => chkMp_31
  | 32, _ => chkMp_32
  | 33, _ => chkMp_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
