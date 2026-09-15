import GNC.Applications.OrbitalFuel.BurnSensitivityFormula
import GNC.Applications.OrbitalFuel.FreeResponseGeometry
import GNC.Applications.OrbitalFuel.SharedBiasGeometry

/-! Exact correspondence between the polynomial expression and terminal
propagation of the planar/normal burn means through the actual SO(3) schedule.
The input speed is left symbolic here; its physical square root is inserted
by the validated flow theorem. -/
noncomputable section
open Matrix
open scoped Matrix
namespace GNC.Applications.OrbitalFuel.BurnSensitivity
open GNC.PolynomialODE GNC.PolynomialOrbitTransition

def packedInput (terminal : Fin 31 → ℝ) (means : Fin 10 → ℝ) (i : Fin 41) : ℝ :=
  if h : i.val < 31 then terminal ⟨i.val,h⟩ else means ⟨i.val-31,by omega⟩

theorem packed_embed (terminal : Fin 31 → ℝ) (means : Fin 10 → ℝ) (i : Fin 31) :
    packedInput terminal means (embed i) = terminal i := by
  simp [packedInput, embed, i.isLt]

theorem packed_mean (terminal : Fin 31 → ℝ) (means : Fin 10 → ℝ) (i : Fin 10) :
    packedInput terminal means (meanSlot i) = means i := by
  simp [packedInput, meanSlot]

theorem lift_value (e : Expr 31) (terminal : Fin 31 → ℝ) (means : Fin 10 → ℝ) :
    (lift e).value (packedInput terminal means) = e.value terminal := by
  simp only [lift, Expr.value_rename, packed_embed]

def normalizedMatrix (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (means : Fin 10 → ℝ) : Matrix (Fin 6) (Fin 3) ℝ :=
  let P : Matrix (Fin 4) (Fin 2) ℝ := F * Matrix.of (fun (r : Fin 4) (c : Fin 2) => means ⟨2*r.val+c.val,by omega⟩)
  let N := H *ᵥ (fun (r : Fin 2) => means ⟨8+r.val,by omega⟩)
  let Q : Matrix (Fin 2) (Fin 2) ℝ := !![z 0*z 4,z 1*z 4; -z 1*z 4,z 0*z 4]
  let position : Matrix (Fin 2) (Fin 2) ℝ := Q * Matrix.of (fun (r : Fin 2) (c : Fin 2) => P ⟨r.val,by omega⟩ c)
  let velocity : Matrix (Fin 2) (Fin 2) ℝ := Q * Matrix.of (fun (r : Fin 2) (c : Fin 2) => P ⟨2+r.val,by omega⟩ c)
  ![![position 0 0,position 0 1,0], ![position 1 0,position 1 1,0], ![0,0,N 0],
    ![velocity 0 0,velocity 0 1,0], ![velocity 1 0,velocity 1 1,0], ![0,0,N 1]]

def physicalMatrix (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed : ℝ) (means : Fin 10 → ℝ) : Matrix (Fin 6) (Fin 3) ℝ := fun i k =>
  (burnScale:ℝ)/(FreeResponse.tolerance i:ℝ)*
    ((if i.val < 3 then (FreeResponse.lengthUnit:ℝ) else speed)*normalizedMatrix z F H means i k)

set_option maxHeartbeats 8000000 in
theorem normalizedEntry_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ)
    (integrals : Fin 4 → ℝ) (means : Fin 10 → ℝ) (i : Fin 6) (k : Fin 3) :
    (normalizedEntry i k).value
      (packedInput (FreeResponse.packedInput z F H speed initialSpeed integrals) means) =
      normalizedMatrix z F H means i k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [normalizedEntry, planeValue, normalValue, planeMean, normalMean,
      Expr.value, lift_value, packed_mean, FreeResponse.planeEntry, FreeResponse.normalEntry,
      FreeResponse.frameEntry, FreeResponse.packedInput, pack, normalizedMatrix,
      Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]
  all_goals ring_nf <;> simp <;> ring

theorem outputEntry_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ)
    (integrals : Fin 4 → ℝ) (means : Fin 10 → ℝ) (i : Fin 6) (k : Fin 3) :
    (outputEntry i k).value
      (packedInput (FreeResponse.packedInput z F H speed initialSpeed integrals) means) =
      physicalMatrix z F H speed means i k := by
  simp only [outputEntry, Expr.value, Rat.cast_div, normalizedEntry_correct]
  unfold physicalMatrix
  split_ifs <;> rfl

set_option maxHeartbeats 8000000 in
theorem rotation_correct (j : Fin 18) (r c : Fin 3) :
    (rotation j r c:ℝ) = (SharedBiasGeometry.cycleRotation j).val r c := by
  fin_cases j <;> fin_cases r <;> fin_cases c <;>
    norm_num [rotation, base, SharedBiasGeometry.cycleRotation, SharedBiasGeometry.baseRotation,
      SharedBiasGeometry.base, SharedBiasGeometry.rollReversal, SharedBiasGeometry.reversal,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

def physicalCoefficient (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed : ℝ) (means : Fin 10 → ℝ)
    (i : Fin 12) (j : Fin 18) (k : Fin 3) : ℝ :=
  (if i.val%2 = 0 then -1 else 1)*
    (physicalMatrix z F H speed means * (SharedBiasGeometry.cycleRotation j).val) ⟨i.val/2,by omega⟩ k

theorem coefficient_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ)
    (integrals : Fin 4 → ℝ) (means : Fin 10 → ℝ) (i : Fin 12) (j : Fin 18) (k : Fin 3) :
    (coefficient i j k).value
      (packedInput (FreeResponse.packedInput z F H speed initialSpeed integrals) means) =
      physicalCoefficient z F H speed means i j k := by
  simp only [coefficient, Expr.value, outputEntry_correct, rotation_correct,
    physicalCoefficient, Matrix.mul_apply, Fin.sum_univ_succ]
  split_ifs <;> norm_num <;> ring

end GNC.Applications.OrbitalFuel.BurnSensitivity
