import GNC.Applications.Rendezvous.HCWMatrix
import GNC.Control.Planner

/-! The constant change from classical LVLH velocity to the paper's log
velocity, and its exact action on the HCW planning blocks. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC.HCWMatrix

def omega (n : ℝ) : Mat3 := skew ![0,0,n]
def changeCoordinates (n : ℝ) : Mat6 := fromBlocks 1 0 (omega n) 1
def changeCoordinatesInv (n : ℝ) : Mat6 := fromBlocks 1 0 (-omega n) 1
def logGravity (n : ℝ) : Mat3 := !![2*n^2,0,0; 0,-n^2,0; 0,0,-n^2]
def logGenerator (n : ℝ) : Mat6 := fromBlocks (-omega n) 1 (logGravity n) (-omega n)
def logSTM (n t : ℝ) : Mat6 := changeCoordinates n*stm n t*changeCoordinatesInv n

theorem change_cancel (n : ℝ) : changeCoordinates n*changeCoordinatesInv n = 1 := by
  simp only [changeCoordinates, changeCoordinatesInv, fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, add_neg_cancel]
  exact fromBlocks_one

theorem change_cancel' (n : ℝ) : changeCoordinatesInv n*changeCoordinates n = 1 := by
  simp only [changeCoordinates, changeCoordinatesInv, fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, neg_add_cancel]
  exact fromBlocks_one

theorem change_generator (n : ℝ) :
    changeCoordinates n*generator n = logGenerator n*changeCoordinates n := by
  simp only [changeCoordinates, generator, logGenerator, fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [omega, skew, gravity, coriolis, logGravity, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_succ] <;> ring

theorem logSTM_derivative (n t : ℝ) (hn : n ≠ 0) :
    HasDerivAt (logSTM n) (logGenerator n*logSTM n t) t := by
  convert ((stm_derivative n t hn).const_mul (changeCoordinates n)).mul_const
    (changeCoordinatesInv n) using 1
  simp only [logSTM, ← Matrix.mul_assoc, change_generator]

@[simp] theorem logSTM_initial (n : ℝ) : logSTM n 0 = 1 := by
  rw [logSTM, stm_initial, Matrix.mul_one, change_cancel]

/-- Both sides of the claimed similarity are actual fundamental solutions. -/
theorem logSTM_exp (n t : ℝ) (hn : n ≠ 0) :
    logSTM n t = NormedSpace.exp (t • logGenerator n) := by
  have h := MixedInvariant.flow_unique (logGenerator n) 0 1 (logSTM n)
    (fun s => by simpa using logSTM_derivative n s hn) (logSTM_initial n)
  simpa [MixedInvariant.flow] using congrFun h t

/-- The top row transformation in the proof of Corollary 3. -/
theorem logSTM_pp (n t : ℝ) : (logSTM n t).toBlocks₁₁ = rr n t-rv n t*omega n := by
  simp [logSTM, changeCoordinates, changeCoordinatesInv, stm, fromBlocks_multiply,
    Matrix.mul_neg, sub_eq_add_neg]

/-- Equation (91): the position-velocity block is unchanged. -/
theorem logSTM_pv (n t : ℝ) : (logSTM n t).toBlocks₁₂ = rv n t := by
  simp [logSTM, changeCoordinates, changeCoordinatesInv, stm, fromBlocks_multiply]

theorem logSTM_vv (n t : ℝ) : (logSTM n t).toBlocks₂₂ = omega n*rv n t+vv n t := by
  simp [logSTM, changeCoordinates, changeCoordinatesInv, stm, fromBlocks_multiply]

/-- The algebraic planner is instantiated by the checked HCW transition
matrix. Its pv equivalence must represent the actual nonsingular rv block. -/
def transfer (n t : ℝ) (pv : Vec3 ≃ₗ[ℝ] Vec3) : Planner.Transfer Vec3 where
  pp := ((logSTM n t).toBlocks₁₁).mulVecLin
  pv := pv
  pR := 0
  vp := ((logSTM n t).toBlocks₂₁).mulVecLin
  vv := ((logSTM n t).toBlocks₂₂).mulVecLin
  vR := 0
  bp := 0
  bv := 0

/-- Equation (92), including the velocity-coordinate change: the log solve
is exactly the classical HCW departure impulse. -/
theorem departure_classical (n t : ℝ) (pv : Vec3 ≃ₗ[ℝ] Vec3)
    (hpv : ∀ v, pv v = rv n t *ᵥ v) (p u : Vec3) :
    (transfer n t pv).departure p (u+omega n *ᵥ p) 0 =
      -u-pv.symm (rr n t *ᵥ p) := by
  simp only [Planner.Transfer.departure, transfer, LinearMap.zero_apply, add_zero]
  change -(u+omega n *ᵥ p)-pv.symm ((logSTM n t).toBlocks₁₁ *ᵥ p) = _
  rw [logSTM_pp, Matrix.sub_mulVec, ← mulVec_mulVec, map_sub, ← hpv,
    LinearEquiv.symm_apply_apply]
  abel

end GNC.HCWMatrix
