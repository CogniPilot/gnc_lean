import GNC.Applications.CertifiedBurn.Steps

/-! The full-row transition pair checks of the burn certificate chain at every node, one
kernel decision per node. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn

theorem chkMf_00 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 0 := by decide +kernel
theorem chkMf_01 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 1 := by decide +kernel
theorem chkMf_02 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 2 := by decide +kernel
theorem chkMf_03 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 3 := by decide +kernel
theorem chkMf_04 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 4 := by decide +kernel
theorem chkMf_05 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 5 := by decide +kernel
theorem chkMf_06 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 6 := by decide +kernel
theorem chkMf_07 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 7 := by decide +kernel
theorem chkMf_08 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 8 := by decide +kernel
theorem chkMf_09 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 9 := by decide +kernel
theorem chkMf_10 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 10 := by decide +kernel
theorem chkMf_11 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 11 := by decide +kernel
theorem chkMf_12 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 12 := by decide +kernel
theorem chkMf_13 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 13 := by decide +kernel
theorem chkMf_14 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 14 := by decide +kernel
theorem chkMf_15 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 15 := by decide +kernel
theorem chkMf_16 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 16 := by decide +kernel
theorem chkMf_17 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 17 := by decide +kernel
theorem chkMf_18 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 18 := by decide +kernel
theorem chkMf_19 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 19 := by decide +kernel
theorem chkMf_20 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 20 := by decide +kernel
theorem chkMf_21 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 21 := by decide +kernel
theorem chkMf_22 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 22 := by decide +kernel
theorem chkMf_23 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 23 := by decide +kernel
theorem chkMf_24 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 24 := by decide +kernel
theorem chkMf_25 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 25 := by decide +kernel
theorem chkMf_26 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 26 := by decide +kernel
theorem chkMf_27 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 27 := by decide +kernel
theorem chkMf_28 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 28 := by decide +kernel
theorem chkMf_29 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 29 := by decide +kernel
theorem chkMf_30 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 30 := by decide +kernel
theorem chkMf_31 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 31 := by decide +kernel
theorem chkMf_32 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 32 := by decide +kernel
theorem chkMf_33 : pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) 33 := by decide +kernel

theorem chkMf : ∀ i, i ≤ 33 → pairChecksM steps Finset.univ (fun r => r.kM) (fun r => r.kS) i
  | 0, _ => chkMf_00
  | 1, _ => chkMf_01
  | 2, _ => chkMf_02
  | 3, _ => chkMf_03
  | 4, _ => chkMf_04
  | 5, _ => chkMf_05
  | 6, _ => chkMf_06
  | 7, _ => chkMf_07
  | 8, _ => chkMf_08
  | 9, _ => chkMf_09
  | 10, _ => chkMf_10
  | 11, _ => chkMf_11
  | 12, _ => chkMf_12
  | 13, _ => chkMf_13
  | 14, _ => chkMf_14
  | 15, _ => chkMf_15
  | 16, _ => chkMf_16
  | 17, _ => chkMf_17
  | 18, _ => chkMf_18
  | 19, _ => chkMf_19
  | 20, _ => chkMf_20
  | 21, _ => chkMf_21
  | 22, _ => chkMf_22
  | 23, _ => chkMf_23
  | 24, _ => chkMf_24
  | 25, _ => chkMf_25
  | 26, _ => chkMf_26
  | 27, _ => chkMf_27
  | 28, _ => chkMf_28
  | 29, _ => chkMf_29
  | 30, _ => chkMf_30
  | 31, _ => chkMf_31
  | 32, _ => chkMf_32
  | 33, _ => chkMf_33
  | k + 34, h => absurd h (by omega)

end GNC.Applications.CertifiedBurn.Orbit
