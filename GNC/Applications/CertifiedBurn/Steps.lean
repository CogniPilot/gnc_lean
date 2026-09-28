import GNC.Applications.CertifiedBurn.Data.Step00
import GNC.Applications.CertifiedBurn.Data.Step01
import GNC.Applications.CertifiedBurn.Data.Step02
import GNC.Applications.CertifiedBurn.Data.Step03
import GNC.Applications.CertifiedBurn.Data.Step04
import GNC.Applications.CertifiedBurn.Data.Step05
import GNC.Applications.CertifiedBurn.Data.Step06
import GNC.Applications.CertifiedBurn.Data.Step07
import GNC.Applications.CertifiedBurn.Data.Step08
import GNC.Applications.CertifiedBurn.Data.Step09
import GNC.Applications.CertifiedBurn.Data.Step10
import GNC.Applications.CertifiedBurn.Data.Step11
import GNC.Applications.CertifiedBurn.Data.Step12
import GNC.Applications.CertifiedBurn.Data.Step13
import GNC.Applications.CertifiedBurn.Data.Step14
import GNC.Applications.CertifiedBurn.Data.Step15
import GNC.Applications.CertifiedBurn.Data.Step16
import GNC.Applications.CertifiedBurn.Data.Step17
import GNC.Applications.CertifiedBurn.Data.Step18
import GNC.Applications.CertifiedBurn.Data.Step19
import GNC.Applications.CertifiedBurn.Data.Step20
import GNC.Applications.CertifiedBurn.Data.Step21
import GNC.Applications.CertifiedBurn.Data.Step22
import GNC.Applications.CertifiedBurn.Data.Step23
import GNC.Applications.CertifiedBurn.Data.Step24
import GNC.Applications.CertifiedBurn.Data.Step25
import GNC.Applications.CertifiedBurn.Data.Step26
import GNC.Applications.CertifiedBurn.Data.Step27
import GNC.Applications.CertifiedBurn.Data.Step28
import GNC.Applications.CertifiedBurn.Data.Step29
import GNC.Applications.CertifiedBurn.Data.Step30
import GNC.Applications.CertifiedBurn.Data.Step31
import GNC.Applications.CertifiedBurn.Data.Step32
import GNC.Applications.CertifiedBurn.Data.Step33
import GNC.Applications.CertifiedBurn.Ledger
import GNC.Applications.CertifiedBurn.Chain

/-! The step list of the burn certificate chain, the validity of every step,
and the junction, initial and ledger checks of the chain. The theorem statements
live in `GNC.Applications.CertifiedBurn.Orbit`. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Set Finset Matrix
open GNC.Planning.PolynomialKernel GNC.PolynomialBounds
namespace GNC.Applications.CertifiedBurn.Orbit
open GNC.Applications.CertifiedBurn GNC.PlanarCoast GNC.PlanarBurn
open scoped RealInnerProductSpace

/-- The 34 certified steps (the last step continues the tail). -/
def steps : ℕ → BurnStep
  | 0 => Data.Step00.rec
  | 1 => Data.Step01.rec
  | 2 => Data.Step02.rec
  | 3 => Data.Step03.rec
  | 4 => Data.Step04.rec
  | 5 => Data.Step05.rec
  | 6 => Data.Step06.rec
  | 7 => Data.Step07.rec
  | 8 => Data.Step08.rec
  | 9 => Data.Step09.rec
  | 10 => Data.Step10.rec
  | 11 => Data.Step11.rec
  | 12 => Data.Step12.rec
  | 13 => Data.Step13.rec
  | 14 => Data.Step14.rec
  | 15 => Data.Step15.rec
  | 16 => Data.Step16.rec
  | 17 => Data.Step17.rec
  | 18 => Data.Step18.rec
  | 19 => Data.Step19.rec
  | 20 => Data.Step20.rec
  | 21 => Data.Step21.rec
  | 22 => Data.Step22.rec
  | 23 => Data.Step23.rec
  | 24 => Data.Step24.rec
  | 25 => Data.Step25.rec
  | 26 => Data.Step26.rec
  | 27 => Data.Step27.rec
  | 28 => Data.Step28.rec
  | 29 => Data.Step29.rec
  | 30 => Data.Step30.rec
  | 31 => Data.Step31.rec
  | 32 => Data.Step32.rec
  | _ => Data.Step33.rec

/-- Every step's rational certificate is valid. -/
theorem valid_all (j : ℕ) : (steps j).Valid := by
  unfold steps
  split
  · exact Data.Step00.valid
  · exact Data.Step01.valid
  · exact Data.Step02.valid
  · exact Data.Step03.valid
  · exact Data.Step04.valid
  · exact Data.Step05.valid
  · exact Data.Step06.valid
  · exact Data.Step07.valid
  · exact Data.Step08.valid
  · exact Data.Step09.valid
  · exact Data.Step10.valid
  · exact Data.Step11.valid
  · exact Data.Step12.valid
  · exact Data.Step13.valid
  · exact Data.Step14.valid
  · exact Data.Step15.valid
  · exact Data.Step16.valid
  · exact Data.Step17.valid
  · exact Data.Step18.valid
  · exact Data.Step19.valid
  · exact Data.Step20.valid
  · exact Data.Step21.valid
  · exact Data.Step22.valid
  · exact Data.Step23.valid
  · exact Data.Step24.valid
  · exact Data.Step25.valid
  · exact Data.Step26.valid
  · exact Data.Step27.valid
  · exact Data.Step28.valid
  · exact Data.Step29.valid
  · exact Data.Step30.valid
  · exact Data.Step31.valid
  · exact Data.Step32.valid
  · exact Data.Step33.valid

theorem steps_tail (j : ℕ) (hj : 33 ≤ j) : steps j = steps 33 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 33 := ⟨j - 33, by omega⟩
  rfl

theorem steps_min (j : ℕ) : steps (min j 33) = steps j := by
  by_cases hj : j ≤ 33
  · rw [min_eq_left hj]
  · rw [min_eq_right (by omega), steps_tail j (by omega)]

/-- Every step carries the misalignment bound of the ledger. -/
theorem alpha_all : ∀ j ∈ Finset.range 34, (steps j).bc.alpha = Ledger.alpha := by
  intro j hj; rw [Finset.mem_range] at hj; interval_cases j <;> decide +kernel

theorem alpha_eq (j : ℕ) : (steps j).bc.alpha = Ledger.alpha := by
  rw [← steps_min j]; exact alpha_all _ (Finset.mem_range.mpr (by omega))

/-! ### Junction checks of the chain -/

theorem hEin0 : (steps 0).Ein = Ledger.e0p + Ledger.e0v := by decide +kernel

theorem hEinS : ∀ j, j < 33 →
    (steps (j + 1)).Ein = nodeBoundQ steps Ledger.e0p Ledger.e0v j + (steps (j + 1)).d := by
  intro j hj; interval_cases j <;> decide +kernel

theorem hjX : ∀ j, j < 33 → BurnStep.jumpSqX (steps j) (steps (j + 1)) ≤ (steps (j + 1)).dX ^ 2 := by
  intro j hj; interval_cases j <;> decide +kernel

theorem hjG : ∀ j, j < 33 → BurnStep.jumpSqG (steps j) (steps (j + 1)) ≤ (steps (j + 1)).dG ^ 2 := by
  intro j hj; interval_cases j <;> decide +kernel

/-- The initial sensitivity vanishes and the stored start is within the
initial radii of the exact start `(1, 0, 0, 21/20)`. -/
theorem init_data :
    (steps 0).bc.gx.headI = 0 ∧ (steps 0).bc.gy.headI = 0
    ∧ (steps 0).bc.gvx.headI = 0 ∧ (steps 0).bc.gvy.headI = 0
    ∧ 0 ≤ Ledger.e0p
    ∧ (1 - (steps 0).bc.x.headI) ^ 2 + (0 - (steps 0).bc.y.headI) ^ 2 ≤ Ledger.e0p ^ 2
    ∧ 0 ≤ Ledger.e0v
    ∧ (0 - (differentiate (steps 0).bc.x).headI) ^ 2
        + (21 / 20 - (differentiate (steps 0).bc.y).headI) ^ 2 ≤ Ledger.e0v ^ 2 := by
  decide +kernel

/-- The composed node bounds are the ledger values. -/
theorem pos_ledger : ∀ i ∈ Finset.range 34,
    nodePosQ steps Ledger.e0p Ledger.e0v i = Ledger.posBounds.getD i 0 := by
  intro i hi; rw [Finset.mem_range] at hi; interval_cases i <;> decide +kernel

theorem vel_ledger : ∀ i ∈ Finset.range 34,
    nodeVelQ steps Ledger.e0p Ledger.e0v i = Ledger.velBounds.getD i 0 := by
  intro i hi; rw [Finset.mem_range] at hi; interval_cases i <;> decide +kernel

end GNC.Applications.CertifiedBurn.Orbit
