import GNC.Applications.CertifiedCoast.Curvature.Data.Step00
import GNC.Applications.CertifiedCoast.Curvature.Data.Step01
import GNC.Applications.CertifiedCoast.Curvature.Data.Step02
import GNC.Applications.CertifiedCoast.Curvature.Data.Step03
import GNC.Applications.CertifiedCoast.Curvature.Data.Step04
import GNC.Applications.CertifiedCoast.Curvature.Data.Step05
import GNC.Applications.CertifiedCoast.Curvature.Data.Step06
import GNC.Applications.CertifiedCoast.Curvature.Data.Step07
import GNC.Applications.CertifiedCoast.Curvature.Data.Step08
import GNC.Applications.CertifiedCoast.Curvature.Data.Step09
import GNC.Applications.CertifiedCoast.Curvature.Data.Step10
import GNC.Applications.CertifiedCoast.Curvature.Data.Step11
import GNC.Applications.CertifiedCoast.Curvature.Data.Step12
import GNC.Applications.CertifiedCoast.Curvature.Data.Step13
import GNC.Applications.CertifiedCoast.Curvature.Data.Step14
import GNC.Applications.CertifiedCoast.Curvature.Data.Step15
import GNC.Applications.CertifiedCoast.Curvature.Data.Step16
import GNC.Applications.CertifiedCoast.Curvature.Data.Step17
import GNC.Applications.CertifiedCoast.Curvature.Data.Step18
import GNC.Applications.CertifiedCoast.Curvature.Data.Step19
import GNC.Applications.CertifiedCoast.Curvature.Data.Step20
import GNC.Applications.CertifiedCoast.Curvature.Data.Step21
import GNC.Applications.CertifiedCoast.Curvature.Data.Step22
import GNC.Applications.CertifiedCoast.Curvature.Data.Step23
import GNC.Applications.CertifiedCoast.Curvature.Data.Step24
import GNC.Applications.CertifiedCoast.Curvature.Data.Step25
import GNC.Applications.CertifiedCoast.Curvature.Data.Step26
import GNC.Applications.CertifiedCoast.Curvature.Data.Step27
import GNC.Applications.CertifiedCoast.Curvature.Data.Step28
import GNC.Applications.CertifiedCoast.Curvature.Data.Step29
import GNC.Applications.CertifiedCoast.Curvature.Data.Step30
import GNC.Applications.CertifiedCoast.Curvature.Data.Step31
import GNC.Applications.CertifiedCoast.Curvature.Ledger
import GNC.Applications.CertifiedCoast.Curvature.Chain

/-! Whole-orbit curvature certificate: 32 certified coast steps of a degree-20
Taylor integrator over one Kepler period. Each step's rational curvature
certificate is checked by the kernel through `StepRecord.Valid`, and the exact
composed transitions certify the terminal error bound of every true
inverse-square solution seeded within the initial radii, via
`chain_terminal_bounds`. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Set Finset Matrix
namespace GNC.Applications.CertifiedCoast.Curvature.Orbit
open GNC.Applications.CertifiedCoast.Curvature GNC.PlanarCoast GNC.PlanarCoast.Candidate

/-- The 32 certified curvature steps of the coast (step 31 continues the tail). -/
def steps : ℕ → StepRecord
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
  | _ => Data.Step31.rec

/-- Every step's rational curvature certificate is valid. -/
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

/-- The stored handoff radius of every step is nonnegative. -/
theorem d_nonneg (j : ℕ) : 0 ≤ (steps j).d := by
  unfold steps; split <;> decide +kernel

/-- Evaluated local transitions of the chain. -/
def Pq (k : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := (steps k).Pev

/-- Real endpoint transitions of the chain. -/
def P (k : ℕ) : Matrix (Fin 4) (Fin 4) ℝ := ((steps k).Pev).map (Rat.cast : ℚ → ℝ)

theorem hP (k : ℕ) : P k = realMat (steps k).cc.G ((steps k).cc.h : ℝ) :=
  (StepRecord.P_eq (steps k) (valid_all k)).symm

/-! ### Rational pair checks of the composed transitions -/

/-- Full-row composed-transition Frobenius-square checks for every node. -/
theorem pairFull : ∀ i ∈ Finset.range 32, ∀ j ∈ Finset.range (i + 1),
    0 ≤ (steps i).kM.getD j 0
    ∧ (∑ r, ∑ c, (stmQ Pq i j r c) ^ 2) ≤ ((steps i).kM.getD j 0) ^ 2
    ∧ 0 ≤ (steps i).kS.getD j 0
    ∧ (∑ r, ∑ c, (stmQ Pq i (j + 1) r c) ^ 2) ≤ ((steps i).kS.getD j 0) ^ 2 := by
  intro i hi; rw [Finset.mem_range] at hi; interval_cases i <;> decide +kernel

/-- Position-row composed-transition checks at the terminal node. -/
theorem pairPos : ∀ j ∈ Finset.range 32,
    0 ≤ (steps 31).kMp.getD j 0
    ∧ (∑ r ∈ ({0, 1} : Finset (Fin 4)), ∑ c, (stmQ Pq 31 j r c) ^ 2)
        ≤ ((steps 31).kMp.getD j 0) ^ 2
    ∧ 0 ≤ (steps 31).kSp.getD j 0
    ∧ (∑ r ∈ ({0, 1} : Finset (Fin 4)), ∑ c, (stmQ Pq 31 (j + 1) r c) ^ 2)
        ≤ ((steps 31).kSp.getD j 0) ^ 2 := by
  intro j hj; rw [Finset.mem_range] at hj; interval_cases j <;> decide +kernel

/-- Velocity-row composed-transition checks at the terminal node. -/
theorem pairVel : ∀ j ∈ Finset.range 32,
    0 ≤ (steps 31).kMv.getD j 0
    ∧ (∑ r ∈ ({2, 3} : Finset (Fin 4)), ∑ c, (stmQ Pq 31 j r c) ^ 2)
        ≤ ((steps 31).kMv.getD j 0) ^ 2
    ∧ 0 ≤ (steps 31).kSv.getD j 0
    ∧ (∑ r ∈ ({2, 3} : Finset (Fin 4)), ∑ c, (stmQ Pq 31 (j + 1) r c) ^ 2)
        ≤ ((steps 31).kSv.getD j 0) ^ 2 := by
  intro j hj; rw [Finset.mem_range] at hj; interval_cases j <;> decide +kernel

/-! ### Tight per-pair velocity-column kernel checks -/

/-- Full-row tight velocity-column kernel checks for every node: the polynomial
product `Φ i j · H_j`, restricted to the velocity columns, is bounded by
`kV_ij`. -/
theorem pairVfull : ∀ i ∈ Finset.range 32, ∀ j ∈ Finset.range (i + 1),
    0 ≤ (steps i).kV.getD j 0
    ∧ matSumSqRowsVel (cMul (stmQ Pq i j) (steps j).cc.H) (steps j).cc.h Finset.univ
        ≤ ((steps i).kV.getD j 0) ^ 2 := by
  intro i hi; rw [Finset.mem_range] at hi; interval_cases i <;> decide +kernel

/-- Position-row tight velocity-column kernel checks at the terminal node. -/
theorem pairVpos : ∀ j ∈ Finset.range 32,
    0 ≤ (steps 31).kVp.getD j 0
    ∧ matSumSqRowsVel (cMul (stmQ Pq 31 j) (steps j).cc.H) (steps j).cc.h
        ({0, 1} : Finset (Fin 4)) ≤ ((steps 31).kVp.getD j 0) ^ 2 := by
  intro j hj; rw [Finset.mem_range] at hj; interval_cases j <;> decide +kernel

/-- Velocity-row tight velocity-column kernel checks at the terminal node. -/
theorem pairVvel : ∀ j ∈ Finset.range 32,
    0 ≤ (steps 31).kVv.getD j 0
    ∧ matSumSqRowsVel (cMul (stmQ Pq 31 j) (steps j).cc.H) (steps j).cc.h
        ({2, 3} : Finset (Fin 4)) ≤ ((steps 31).kVv.getD j 0) ^ 2 := by
  intro j hj; rw [Finset.mem_range] at hj; interval_cases j <;> decide +kernel

/-! ### Column-split checks of the initial composed transition `Φ i 0` -/

/-- Full-row column-split checks of `Φ i 0` for every node. -/
theorem pairInitFull : ∀ i ∈ Finset.range 32,
    0 ≤ (steps i).kM0p
    ∧ (∑ r, ∑ c ∈ ({0, 1} : Finset (Fin 4)), (stmQ Pq i 0 r c) ^ 2) ≤ ((steps i).kM0p) ^ 2
    ∧ 0 ≤ (steps i).kM0v
    ∧ (∑ r, ∑ c ∈ ({2, 3} : Finset (Fin 4)), (stmQ Pq i 0 r c) ^ 2) ≤ ((steps i).kM0v) ^ 2 := by
  intro i hi; rw [Finset.mem_range] at hi; interval_cases i <;> decide +kernel

/-- Position-row column-split checks of `Φ 31 0` at the terminal node. -/
theorem pairInitPos :
    0 ≤ (steps 31).kMp0p
    ∧ (∑ r ∈ ({0, 1} : Finset (Fin 4)), ∑ c ∈ ({0, 1} : Finset (Fin 4)), (stmQ Pq 31 0 r c) ^ 2)
        ≤ ((steps 31).kMp0p) ^ 2
    ∧ 0 ≤ (steps 31).kMp0v
    ∧ (∑ r ∈ ({0, 1} : Finset (Fin 4)), ∑ c ∈ ({2, 3} : Finset (Fin 4)), (stmQ Pq 31 0 r c) ^ 2)
        ≤ ((steps 31).kMp0v) ^ 2 := by decide +kernel

/-- Velocity-row column-split checks of `Φ 31 0` at the terminal node. -/
theorem pairInitVel :
    0 ≤ (steps 31).kMv0p
    ∧ (∑ r ∈ ({2, 3} : Finset (Fin 4)), ∑ c ∈ ({0, 1} : Finset (Fin 4)), (stmQ Pq 31 0 r c) ^ 2)
        ≤ ((steps 31).kMv0p) ^ 2
    ∧ 0 ≤ (steps 31).kMv0v
    ∧ (∑ r ∈ ({2, 3} : Finset (Fin 4)), ∑ c ∈ ({2, 3} : Finset (Fin 4)), (stmQ Pq 31 0 r c) ^ 2)
        ≤ ((steps 31).kMv0v) ^ 2 := by decide +kernel

theorem hkMf : ∀ i, i ≤ 31 → ∀ j, j ≤ i →
    GNC.Transported.frobRows Finset.univ (GNC.Transported.stm P i j)
      ≤ ((steps i).kM.getD j 0 : ℝ) := by
  intro i hi j hj
  have hp := pairFull i (Finset.mem_range.mpr (by omega)) j (Finset.mem_range.mpr (by omega))
  exact stm_frobRows_le steps Finset.univ i j ((steps i).kM.getD j 0) hp.1 hp.2.1

theorem hkSf : ∀ i, i ≤ 31 → ∀ j, j ≤ i →
    GNC.Transported.frobRows Finset.univ (GNC.Transported.stm P i (j + 1))
      ≤ ((steps i).kS.getD j 0 : ℝ) := by
  intro i hi j hj
  have hp := pairFull i (Finset.mem_range.mpr (by omega)) j (Finset.mem_range.mpr (by omega))
  exact stm_frobRows_le steps Finset.univ i (j + 1) ((steps i).kS.getD j 0) hp.2.2.1 hp.2.2.2

theorem hkMp : ∀ j, j ≤ 31 →
    GNC.Transported.frobRows ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P 31 j)
      ≤ ((steps 31).kMp.getD j 0 : ℝ) := by
  intro j hj
  have hp := pairPos j (Finset.mem_range.mpr (by omega))
  exact stm_frobRows_le steps ({0, 1} : Finset (Fin 4)) 31 j ((steps 31).kMp.getD j 0) hp.1 hp.2.1

theorem hkSp : ∀ j, j ≤ 31 →
    GNC.Transported.frobRows ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P 31 (j + 1))
      ≤ ((steps 31).kSp.getD j 0 : ℝ) := by
  intro j hj
  have hp := pairPos j (Finset.mem_range.mpr (by omega))
  exact stm_frobRows_le steps ({0, 1} : Finset (Fin 4)) 31 (j + 1) ((steps 31).kSp.getD j 0)
    hp.2.2.1 hp.2.2.2

theorem hkMv : ∀ j, j ≤ 31 →
    GNC.Transported.frobRows ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P 31 j)
      ≤ ((steps 31).kMv.getD j 0 : ℝ) := by
  intro j hj
  have hp := pairVel j (Finset.mem_range.mpr (by omega))
  exact stm_frobRows_le steps ({2, 3} : Finset (Fin 4)) 31 j ((steps 31).kMv.getD j 0) hp.1 hp.2.1

theorem hkSv : ∀ j, j ≤ 31 →
    GNC.Transported.frobRows ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P 31 (j + 1))
      ≤ ((steps 31).kSv.getD j 0 : ℝ) := by
  intro j hj
  have hp := pairVel j (Finset.mem_range.mpr (by omega))
  exact stm_frobRows_le steps ({2, 3} : Finset (Fin 4)) 31 (j + 1) ((steps 31).kSv.getD j 0)
    hp.2.2.1 hp.2.2.2

/-! ### Real tight kernel and column-split initial bounds -/

theorem hkVf : ∀ i, i ≤ 31 → ∀ j, j ≤ i → ∀ s ∈ Icc (0:ℝ) ((steps j).cc.h : ℝ),
    GNC.Transported.frobRowsVel Finset.univ (GNC.Transported.stm P i j * (steps j).HfC s)
      ≤ ((steps i).kV.getD j 0 : ℝ) := by
  intro i hi j hj s hs
  have hp := pairVfull i (Finset.mem_range.mpr (by omega)) j (Finset.mem_range.mpr (by omega))
  have habs : |s| ≤ ((steps j).cc.h : ℝ) := by rw [abs_of_nonneg hs.1]; exact hs.2
  exact stm_frobRowsVel_kernel_le steps Finset.univ i j (steps j).cc.H habs
    ((steps i).kV.getD j 0) hp.1 hp.2

theorem hkVp : ∀ j, j ≤ 31 → ∀ s ∈ Icc (0:ℝ) ((steps j).cc.h : ℝ),
    GNC.Transported.frobRowsVel ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P 31 j * (steps j).HfC s)
      ≤ ((steps 31).kVp.getD j 0 : ℝ) := by
  intro j hj s hs
  have hp := pairVpos j (Finset.mem_range.mpr (by omega))
  have habs : |s| ≤ ((steps j).cc.h : ℝ) := by rw [abs_of_nonneg hs.1]; exact hs.2
  exact stm_frobRowsVel_kernel_le steps ({0, 1} : Finset (Fin 4)) 31 j (steps j).cc.H habs
    ((steps 31).kVp.getD j 0) hp.1 hp.2

theorem hkVv : ∀ j, j ≤ 31 → ∀ s ∈ Icc (0:ℝ) ((steps j).cc.h : ℝ),
    GNC.Transported.frobRowsVel ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P 31 j * (steps j).HfC s)
      ≤ ((steps 31).kVv.getD j 0 : ℝ) := by
  intro j hj s hs
  have hp := pairVvel j (Finset.mem_range.mpr (by omega))
  have habs : |s| ≤ ((steps j).cc.h : ℝ) := by rw [abs_of_nonneg hs.1]; exact hs.2
  exact stm_frobRowsVel_kernel_le steps ({2, 3} : Finset (Fin 4)) 31 j (steps j).cc.H habs
    ((steps 31).kVv.getD j 0) hp.1 hp.2

theorem hkM0pf : ∀ i, i ≤ 31 →
    GNC.Transported.frobRowsCols Finset.univ ({0, 1} : Finset (Fin 4)) (GNC.Transported.stm P i 0)
      ≤ ((steps i).kM0p : ℝ) := by
  intro i hi
  have hp := pairInitFull i (Finset.mem_range.mpr (by omega))
  exact stm_frobRowsCols_le steps Finset.univ ({0, 1} : Finset (Fin 4)) i 0 ((steps i).kM0p) hp.1 hp.2.1

theorem hkM0vf : ∀ i, i ≤ 31 →
    GNC.Transported.frobRowsCols Finset.univ ({2, 3} : Finset (Fin 4)) (GNC.Transported.stm P i 0)
      ≤ ((steps i).kM0v : ℝ) := by
  intro i hi
  have hp := pairInitFull i (Finset.mem_range.mpr (by omega))
  exact stm_frobRowsCols_le steps Finset.univ ({2, 3} : Finset (Fin 4)) i 0 ((steps i).kM0v)
    hp.2.2.1 hp.2.2.2

theorem hkM0pp :
    GNC.Transported.frobRowsCols ({0, 1} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4))
      (GNC.Transported.stm P 31 0) ≤ ((steps 31).kMp0p : ℝ) :=
  stm_frobRowsCols_le steps ({0, 1} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4)) 31 0
    ((steps 31).kMp0p) pairInitPos.1 pairInitPos.2.1

theorem hkM0vp :
    GNC.Transported.frobRowsCols ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
      (GNC.Transported.stm P 31 0) ≤ ((steps 31).kMp0v : ℝ) :=
  stm_frobRowsCols_le steps ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) 31 0
    ((steps 31).kMp0v) pairInitPos.2.2.1 pairInitPos.2.2.2

theorem hkM0pv :
    GNC.Transported.frobRowsCols ({2, 3} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4))
      (GNC.Transported.stm P 31 0) ≤ ((steps 31).kMv0p : ℝ) :=
  stm_frobRowsCols_le steps ({2, 3} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4)) 31 0
    ((steps 31).kMv0p) pairInitVel.1 pairInitVel.2.1

theorem hkM0vv :
    GNC.Transported.frobRowsCols ({2, 3} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4))
      (GNC.Transported.stm P 31 0) ≤ ((steps 31).kMv0v : ℝ) :=
  stm_frobRowsCols_le steps ({2, 3} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) 31 0
    ((steps 31).kMv0v) pairInitVel.2.2.1 pairInitVel.2.2.2

/-! ### Junction consistency of the chain -/

theorem hEin0 : (steps 0).Ein = Ledger.e0p + Ledger.e0v := by decide +kernel

theorem hEinS : ∀ j, j < 31 →
    (steps (j + 1)).Ein = nodeBoundQ steps Ledger.e0p Ledger.e0v j + (steps (j + 1)).d := by
  intro j hj; interval_cases j <;> decide +kernel

theorem hjump : ∀ j, j < 31 → StepRecord.jumpSq (steps j) (steps (j + 1)) ≤ (steps (j + 1)).d ^ 2 := by
  intro j hj; interval_cases j <;> decide +kernel

/-! ### The certified terminal error bounds -/

/-- Terminal certified position bound (normalized length). -/
theorem posBound_eq :
    nodeBoundRowsQ steps Ledger.e0p Ledger.e0v (fun r => r.kMp) (fun r => r.kSp) (fun r => r.kVp)
      (fun r => r.kMp0p) (fun r => r.kMp0v) 31 = Ledger.posBound := by
  decide +kernel

/-- Terminal certified velocity bound (normalized velocity), the composed
velocity-row node bound plus the kinematic mismatch of the stored velocity
polynomial (a sum-of-coordinate-bounds form, hence a sound upper bound of the
Euclidean `Ledger.velBound`). -/
def velBoundProv : ℚ :=
  nodeBoundRowsQ steps Ledger.e0p Ledger.e0v (fun r => r.kMv) (fun r => r.kSv) (fun r => r.kVv)
      (fun r => r.kMv0p) (fun r => r.kMv0v) 31
    + (steps 31).cc.toCandidate.kinematic

/-- Whole-orbit certified terminal error: every true inverse-square coast
solution threaded through the 32 steps and seeded within the initial radii ends
within the certified position and velocity error bounds (normalized units). -/
theorem orbit_terminal (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j, Continuous (w j))
    (hw : ∀ j, ∀ s ∈ Icc (0:ℝ) ((steps j).cc.h : ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j s)) s)
    (hacc : ∀ j, Continuous (fun s => Gravity.field 1 (truePos (w j) s)))
    (hjoin : ∀ j, j < 31 → w (j + 1) 0 = w j ((steps j).cc.h : ℝ))
    (hinitp : ‖truePos (w 0) 0 - (steps 0).cc.pos 0‖ ≤ (Ledger.e0p : ℝ))
    (hinitv : ‖trueVel (w 0) 0 - (steps 0).cc.dpos 0‖ ≤ (Ledger.e0v : ℝ)) :
    ‖truePos (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.pos ((steps 31).cc.h : ℝ)‖
        ≤ (Ledger.posBound : ℝ)
    ∧ ‖trueVel (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.vel ((steps 31).cc.h : ℝ)‖
        ≤ (velBoundProv : ℝ) := by
  obtain ⟨_, hpos, hvel⟩ := chain_terminal_bounds steps 31 Ledger.e0p Ledger.e0v P hP valid_all
    w hwc hw hacc hjoin hinitp hinitv hEin0 hEinS d_nonneg hjump
    hkMf hkSf hkVf hkM0pf hkM0vf hkMp hkSp hkVp hkM0pp hkM0vp hkMv hkSv hkVv hkM0pv hkM0vv
  refine ⟨hpos.trans (le_of_eq ?_), ?_⟩
  · exact_mod_cast posBound_eq
  · have hh0 : (0:ℝ) ≤ ((steps 31).cc.h : ℝ) := by exact_mod_cast (valid_all 31).1.1.1
    have hkin := (steps 31).cc.toCandidate.kinematic_bound (right_mem_Icc.mpr hh0)
    have hsplit : trueVel (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.vel ((steps 31).cc.h : ℝ)
        = (trueVel (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.dpos ((steps 31).cc.h : ℝ))
          + ((steps 31).cc.dpos ((steps 31).cc.h : ℝ) - (steps 31).cc.vel ((steps 31).cc.h : ℝ)) := by
      abel
    calc ‖trueVel (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.vel ((steps 31).cc.h : ℝ)‖
        = ‖(trueVel (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.dpos ((steps 31).cc.h : ℝ))
            + ((steps 31).cc.dpos ((steps 31).cc.h : ℝ) - (steps 31).cc.vel ((steps 31).cc.h : ℝ))‖ := by
          rw [hsplit]
      _ ≤ ‖trueVel (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.dpos ((steps 31).cc.h : ℝ)‖
            + ‖(steps 31).cc.dpos ((steps 31).cc.h : ℝ) - (steps 31).cc.vel ((steps 31).cc.h : ℝ)‖ :=
          norm_add_le _ _
      _ ≤ (nodeBoundRowsQ steps Ledger.e0p Ledger.e0v (fun r => r.kMv) (fun r => r.kSv)
              (fun r => r.kVv) (fun r => r.kMv0p) (fun r => r.kMv0v) 31 : ℝ)
            + ((steps 31).cc.toCandidate.kinematic : ℝ) := add_le_add hvel hkin
      _ = (velBoundProv : ℝ) := by rw [velBoundProv]; push_cast; ring

/-! ### Physical (SI) rescaling -/

/-- Metres per normalized length unit (perigee radius). -/
def radiusSI : ℚ := 7000000
/-- Metres per second per normalized velocity unit, a rational upper bound of
`sqrt(mu/r_p) = 7546.4 m/s`. -/
def speedSI : ℚ := 75464 / 10

/-- Terminal SI error bounds: position in metres, velocity in metres per second. -/
theorem physical_bounds_SI (w : ℕ → ℝ → Fin 4 → ℝ)
    (hwc : ∀ j, Continuous (w j))
    (hw : ∀ j, ∀ s ∈ Icc (0:ℝ) ((steps j).cc.h : ℝ),
      HasDerivAt (w j) (PolynomialOrbit.physicalRate 0 (w j s)) s)
    (hacc : ∀ j, Continuous (fun s => Gravity.field 1 (truePos (w j) s)))
    (hjoin : ∀ j, j < 31 → w (j + 1) 0 = w j ((steps j).cc.h : ℝ))
    (hinitp : ‖truePos (w 0) 0 - (steps 0).cc.pos 0‖ ≤ (Ledger.e0p : ℝ))
    (hinitv : ‖trueVel (w 0) 0 - (steps 0).cc.dpos 0‖ ≤ (Ledger.e0v : ℝ)) :
    (radiusSI : ℝ) * ‖truePos (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.pos ((steps 31).cc.h : ℝ)‖
        ≤ ((radiusSI * Ledger.posBound : ℚ) : ℝ)
    ∧ (speedSI : ℝ) * ‖trueVel (w 31) ((steps 31).cc.h : ℝ) - (steps 31).cc.vel ((steps 31).cc.h : ℝ)‖
        ≤ ((speedSI * velBoundProv : ℚ) : ℝ) := by
  obtain ⟨hp, hv⟩ := orbit_terminal w hwc hw hacc hjoin hinitp hinitv
  refine ⟨?_, ?_⟩
  · rw [show ((radiusSI * Ledger.posBound : ℚ) : ℝ) = (radiusSI : ℝ) * (Ledger.posBound : ℝ) by push_cast; ring]
    exact mul_le_mul_of_nonneg_left hp (by norm_num [radiusSI])
  · rw [show ((speedSI * velBoundProv : ℚ) : ℝ) = (speedSI : ℝ) * (velBoundProv : ℝ) by push_cast; ring]
    exact mul_le_mul_of_nonneg_left hv (by norm_num [speedSI])

end GNC.Applications.CertifiedCoast.Curvature.Orbit
