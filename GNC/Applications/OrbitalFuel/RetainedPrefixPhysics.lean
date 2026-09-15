import GNC.Applications.OrbitalFuel.RetainedPrefixTheory
import GNC.Applications.OrbitalFuel.ChaserPrefix
import GNC.Applications.OrbitalFuel.BurnSensitivityGeometry
import GNC.Applications.OrbitalFuel.RetainedNormUnits

/-! The accumulated coefficient expressions are the pullback of the actual
prescribed-acceleration burn schedule with one common body-pointing direction.
The target acceleration, signed SO(3) rotations and candidate fractions are
retained exactly. These identities do not discard the nonlinear gravity remainder.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPrefix
open GNC GNC.PolynomialODE GNC.PolynomialOrbitTransition Matrix

def combine (columns : Fin 4 → ℝ) (q : Vec3) : ℝ :=
  columns 0+q 0*columns 1+q 1*columns 2+q 2*columns 3

def command (arc : Fin 37) (q : Vec3) : Vec3 :=
  match burn arc with
  | none => 0
  | some j => (RetainedNormData.fractions j:ℝ) • rotate (SharedBiasGeometry.cycleRotation j) q

theorem plane_combination (arc : Fin 37) (z : Fin 5 → ℝ)
    (F : Matrix (Fin 4) (Fin 4) ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Vec3) (i : Fin 4) :
    combine (fun k => (forcing arc ⟨i.val,by omega⟩ k).value (pack z F H)) q =
      (planeInverse F *ᵥ TargetThrust.forcing (PolynomialTransition.alpha:ℝ) z) i+
      (planeInverse F *ᵥ ChaserResponse.planeBurn (beta:ℝ) z (command arc q)) i := by
  rw [TargetThrust.forcing_pairing]
  cases hb : burn arc with
  | none =>
    fin_cases i <;>
      simp [combine, forcing, hb, command, ChaserResponse.planeBurn, Expr.value,
        PolynomialBurn.observable, planeObservable_correct,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  | some j =>
    have he : command arc q =
        (RetainedNormData.fractions j:ℝ) • ((SharedBiasGeometry.cycleRotation j).val *ᵥ q) := by
      simp only [command,hb,rotate]
    rw [he]
    simp only [ChaserResponse.planeBurn, mulVec_smul, Pi.smul_apply, smul_eq_mul, mulVec_mulVec]
    fin_cases i <;>
      simp [combine, forcing, hb, Expr.value, PolynomialBurn.observable, planeObservable_correct,
        BurnSensitivity.rotation_correct, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem normal_combination (arc : Fin 37) (z : Fin 5 → ℝ)
    (F : Matrix (Fin 4) (Fin 4) ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Vec3) (i : Fin 2) :
    combine (fun k => (forcing arc ⟨4+i.val,by omega⟩ k).value (pack z F H)) q =
      (normalInverse H *ᵥ ChaserResponse.normalBurn (beta:ℝ) (command arc q)) i := by
  cases hb : burn arc with
  | none =>
    fin_cases i <;>
      simp [combine, forcing, hb, command, ChaserResponse.normalBurn, Expr.value,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  | some j =>
    have he : command arc q =
        (RetainedNormData.fractions j:ℝ) • ((SharedBiasGeometry.cycleRotation j).val *ᵥ q) := by
      simp only [command,hb,rotate]
    rw [he]
    fin_cases i <;>
      simp [combine, forcing, hb, Expr.value, PolynomialBurn.observable, normalObservable_correct,
        BurnSensitivity.rotation_correct, ChaserResponse.normalBurn,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem command_schedule (arc : Fin 37) (q : Vec3) (t : ℝ) :
    command arc q = BurnSchedule.input
      (fun j _t => SharedBiasCertificates.Solar.x j • rotate (SharedBiasGeometry.cycleRotation j) q)
      arc.val t := by
  by_cases h : arc.val%2 = 1
  · simp only [command, burn, dif_pos h, BurnSchedule.input,
      dif_pos (show arc.val < 37 ∧ arc.val%2 = 1 from ⟨arc.isLt,h⟩), RetainedNorm.candidate_matches]
  · simp only [command, burn, dif_neg h, BurnSchedule.input,
      dif_neg (show ¬ (arc.val < 37 ∧ arc.val%2 = 1) by tauto)]

end GNC.Applications.OrbitalFuel.RetainedPrefix
