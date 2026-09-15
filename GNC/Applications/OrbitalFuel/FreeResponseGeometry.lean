import GNC.Applications.OrbitalFuel.FreeResponseFormula

/-! The expression certificate computes the physical RTN free response,
including the target forcing and the initial rotating-frame velocity.
-/
noncomputable section
open Matrix
namespace GNC.Applications.OrbitalFuel.FreeResponse
open GNC.PolynomialODE GNC.PolynomialOrbitTransition

def packedInput (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ)
    (integrals : Fin 4 → ℝ) (i : Fin 31) : ℝ :=
  if h : i.val < 25 then pack z F H ⟨i.val,h⟩
  else if i.val = 25 then speed
  else if i.val = 26 then initialSpeed
  else integrals ⟨i.val-27,by omega⟩

def physicalOutput (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ)
    (integrals : Fin 4 → ℝ) : Fin 6 → ℝ :=
  let initial : Fin 4 → ℝ := ![0, -10000000/(lengthUnit:ℝ),
    (5/4)*initialSpeed*(10000000/(lengthUnit:ℝ)), 0]
  let plane := F *ᵥ (initial-(alpha:ℝ) • integrals)
  let normal := H *ᵥ ![1000000/(lengthUnit:ℝ), 0]
  let Q : Matrix (Fin 2) (Fin 2) ℝ := !![z 0*z 4,z 1*z 4; -z 1*z 4,z 0*z 4]
  let position := Q *ᵥ ![plane 0,plane 1]
  let velocity := Q *ᵥ ![plane 2,plane 3]
  ![(lengthUnit:ℝ)*position 0, (lengthUnit:ℝ)*position 1, (lengthUnit:ℝ)*normal 0,
    speed*velocity 0, speed*velocity 1, speed*normal 1]

set_option maxHeartbeats 4000000 in
theorem output_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ)
    (integrals : Fin 4 → ℝ) (i : Fin 6) :
    (output i).value (packedInput z F H speed initialSpeed integrals) =
      physicalOutput z F H speed initialSpeed integrals i := by
  fin_cases i <;>
    norm_num [output, normalizedOutput, planeValue, normalValue, frameEntry,
      planeEntry, normalEntry, sum4, initialPlane, pulledPlane, Expr.value,
      packedInput, physicalOutput, pack, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]
  all_goals first | left | skip
  all_goals ring_nf <;> simp <;> ring

theorem constraintOutput_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ)
    (integrals : Fin 4 → ℝ) (i : Fin 6) :
    (constraintOutput i).value (packedInput z F H speed initialSpeed integrals) =
      physicalOutput z F H speed initialSpeed integrals i/(tolerance i:ℝ) := by
  simp only [constraintOutput, Expr.value, Rat.cast_div, Rat.cast_one, output_correct]
  ring

end GNC.Applications.OrbitalFuel.FreeResponse
