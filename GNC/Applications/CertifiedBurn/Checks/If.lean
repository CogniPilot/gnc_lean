import GNC.Applications.CertifiedBurn.Steps

/-! The full-row initial column-split pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkIf_00 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 0 := by decide +kernel
theorem chkIf_01 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 1 := by decide +kernel
theorem chkIf_02 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 2 := by decide +kernel
theorem chkIf_03 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 3 := by decide +kernel
theorem chkIf_04 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 4 := by decide +kernel
theorem chkIf_05 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 5 := by decide +kernel
theorem chkIf_06 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 6 := by decide +kernel
theorem chkIf_07 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 7 := by decide +kernel
theorem chkIf_08 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 8 := by decide +kernel
theorem chkIf_09 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 9 := by decide +kernel
theorem chkIf_10 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 10 := by decide +kernel
theorem chkIf_11 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 11 := by decide +kernel
theorem chkIf_12 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 12 := by decide +kernel
theorem chkIf_13 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 13 := by decide +kernel
theorem chkIf_14 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 14 := by decide +kernel
theorem chkIf_15 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 15 := by decide +kernel
theorem chkIf_16 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 16 := by decide +kernel
theorem chkIf_17 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 17 := by decide +kernel
theorem chkIf_18 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 18 := by decide +kernel
theorem chkIf_19 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 19 := by decide +kernel
theorem chkIf_20 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 20 := by decide +kernel
theorem chkIf_21 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 21 := by decide +kernel
theorem chkIf_22 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 22 := by decide +kernel
theorem chkIf_23 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 23 := by decide +kernel
theorem chkIf_24 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 24 := by decide +kernel
theorem chkIf_25 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 25 := by decide +kernel
theorem chkIf_26 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 26 := by decide +kernel
theorem chkIf_27 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 27 := by decide +kernel
theorem chkIf_28 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 28 := by decide +kernel
theorem chkIf_29 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 29 := by decide +kernel
theorem chkIf_30 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 30 := by decide +kernel
theorem chkIf_31 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 31 := by decide +kernel
theorem chkIf_32 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 32 := by decide +kernel
theorem chkIf_33 : initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) 33 := by decide +kernel

theorem chkIf : ∀ i, i ≤ 33 → initChecks steps Finset.univ (fun r => r.kM0p) (fun r => r.kM0v) i
  | 0, _ => chkIf_00
  | 1, _ => chkIf_01
  | 2, _ => chkIf_02
  | 3, _ => chkIf_03
  | 4, _ => chkIf_04
  | 5, _ => chkIf_05
  | 6, _ => chkIf_06
  | 7, _ => chkIf_07
  | 8, _ => chkIf_08
  | 9, _ => chkIf_09
  | 10, _ => chkIf_10
  | 11, _ => chkIf_11
  | 12, _ => chkIf_12
  | 13, _ => chkIf_13
  | 14, _ => chkIf_14
  | 15, _ => chkIf_15
  | 16, _ => chkIf_16
  | 17, _ => chkIf_17
  | 18, _ => chkIf_18
  | 19, _ => chkIf_19
  | 20, _ => chkIf_20
  | 21, _ => chkIf_21
  | 22, _ => chkIf_22
  | 23, _ => chkIf_23
  | 24, _ => chkIf_24
  | 25, _ => chkIf_25
  | 26, _ => chkIf_26
  | 27, _ => chkIf_27
  | 28, _ => chkIf_28
  | 29, _ => chkIf_29
  | 30, _ => chkIf_30
  | 31, _ => chkIf_31
  | 32, _ => chkIf_32
  | 33, _ => chkIf_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
