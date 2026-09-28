import GNC.Applications.CertifiedBurn.Steps

/-! The full-row velocity-column kernel pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkVf_00 : pairChecksV steps Finset.univ (fun r => r.kV) 0 := by decide +kernel
theorem chkVf_01 : pairChecksV steps Finset.univ (fun r => r.kV) 1 := by decide +kernel
theorem chkVf_02 : pairChecksV steps Finset.univ (fun r => r.kV) 2 := by decide +kernel
theorem chkVf_03 : pairChecksV steps Finset.univ (fun r => r.kV) 3 := by decide +kernel
theorem chkVf_04 : pairChecksV steps Finset.univ (fun r => r.kV) 4 := by decide +kernel
theorem chkVf_05 : pairChecksV steps Finset.univ (fun r => r.kV) 5 := by decide +kernel
theorem chkVf_06 : pairChecksV steps Finset.univ (fun r => r.kV) 6 := by decide +kernel
theorem chkVf_07 : pairChecksV steps Finset.univ (fun r => r.kV) 7 := by decide +kernel
theorem chkVf_08 : pairChecksV steps Finset.univ (fun r => r.kV) 8 := by decide +kernel
theorem chkVf_09 : pairChecksV steps Finset.univ (fun r => r.kV) 9 := by decide +kernel
theorem chkVf_10 : pairChecksV steps Finset.univ (fun r => r.kV) 10 := by decide +kernel
theorem chkVf_11 : pairChecksV steps Finset.univ (fun r => r.kV) 11 := by decide +kernel
theorem chkVf_12 : pairChecksV steps Finset.univ (fun r => r.kV) 12 := by decide +kernel
theorem chkVf_13 : pairChecksV steps Finset.univ (fun r => r.kV) 13 := by decide +kernel
theorem chkVf_14 : pairChecksV steps Finset.univ (fun r => r.kV) 14 := by decide +kernel
theorem chkVf_15 : pairChecksV steps Finset.univ (fun r => r.kV) 15 := by decide +kernel
theorem chkVf_16 : pairChecksV steps Finset.univ (fun r => r.kV) 16 := by decide +kernel
theorem chkVf_17 : pairChecksV steps Finset.univ (fun r => r.kV) 17 := by decide +kernel
theorem chkVf_18 : pairChecksV steps Finset.univ (fun r => r.kV) 18 := by decide +kernel
theorem chkVf_19 : pairChecksV steps Finset.univ (fun r => r.kV) 19 := by decide +kernel
theorem chkVf_20 : pairChecksV steps Finset.univ (fun r => r.kV) 20 := by decide +kernel
theorem chkVf_21 : pairChecksV steps Finset.univ (fun r => r.kV) 21 := by decide +kernel
theorem chkVf_22 : pairChecksV steps Finset.univ (fun r => r.kV) 22 := by decide +kernel
theorem chkVf_23 : pairChecksV steps Finset.univ (fun r => r.kV) 23 := by decide +kernel
theorem chkVf_24 : pairChecksV steps Finset.univ (fun r => r.kV) 24 := by decide +kernel
theorem chkVf_25 : pairChecksV steps Finset.univ (fun r => r.kV) 25 := by decide +kernel
theorem chkVf_26 : pairChecksV steps Finset.univ (fun r => r.kV) 26 := by decide +kernel
theorem chkVf_27 : pairChecksV steps Finset.univ (fun r => r.kV) 27 := by decide +kernel
theorem chkVf_28 : pairChecksV steps Finset.univ (fun r => r.kV) 28 := by decide +kernel
theorem chkVf_29 : pairChecksV steps Finset.univ (fun r => r.kV) 29 := by decide +kernel
theorem chkVf_30 : pairChecksV steps Finset.univ (fun r => r.kV) 30 := by decide +kernel
theorem chkVf_31 : pairChecksV steps Finset.univ (fun r => r.kV) 31 := by decide +kernel
theorem chkVf_32 : pairChecksV steps Finset.univ (fun r => r.kV) 32 := by decide +kernel
theorem chkVf_33 : pairChecksV steps Finset.univ (fun r => r.kV) 33 := by decide +kernel

theorem chkVf : ∀ i, i ≤ 33 → pairChecksV steps Finset.univ (fun r => r.kV) i
  | 0, _ => chkVf_00
  | 1, _ => chkVf_01
  | 2, _ => chkVf_02
  | 3, _ => chkVf_03
  | 4, _ => chkVf_04
  | 5, _ => chkVf_05
  | 6, _ => chkVf_06
  | 7, _ => chkVf_07
  | 8, _ => chkVf_08
  | 9, _ => chkVf_09
  | 10, _ => chkVf_10
  | 11, _ => chkVf_11
  | 12, _ => chkVf_12
  | 13, _ => chkVf_13
  | 14, _ => chkVf_14
  | 15, _ => chkVf_15
  | 16, _ => chkVf_16
  | 17, _ => chkVf_17
  | 18, _ => chkVf_18
  | 19, _ => chkVf_19
  | 20, _ => chkVf_20
  | 21, _ => chkVf_21
  | 22, _ => chkVf_22
  | 23, _ => chkVf_23
  | 24, _ => chkVf_24
  | 25, _ => chkVf_25
  | 26, _ => chkVf_26
  | 27, _ => chkVf_27
  | 28, _ => chkVf_28
  | 29, _ => chkVf_29
  | 30, _ => chkVf_30
  | 31, _ => chkVf_31
  | 32, _ => chkVf_32
  | 33, _ => chkVf_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
