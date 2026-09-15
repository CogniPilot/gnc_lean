import GNC.Dynamics.PlanarBurnObservable
import GNC.Dynamics.PlanarChaserError
import GNC.Dynamics.PlanarAttitudeFrame

/-! Constant inertial burn inputs in the exact planar gravity variation.
The pullback observables are linear in the fundamental matrix entries;
the reference-frame rotation cancels before integration. -/
noncomputable section
set_option autoImplicit false
namespace GNC.PolynomialOrbitTransition
open PolynomialODE Matrix
open scoped Matrix

def inertialPlaneInjection : Matrix (Fin 4) (Fin 2) ℝ := !![0,0; 0,0; 1,0; 0,1]

theorem inverseColumn_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 4) (k : Fin 2) :
    (inverseColumn i k).value (pack z F H) = planeInverse F i ⟨2+k.val,by omega⟩ := by
  fin_cases i <;> fin_cases k <;>
    norm_num [inverseColumn, Expr.value, planeInverse, planeForm, pack, planeIndex,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      cons_val_two, cons_val_three, cons_val_four]
  all_goals rfl

theorem inertial_observable_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 4) (k : Fin 2) :
    (inverseColumn i k).value (pack z F H) = (planeInverse F*inertialPlaneInjection) i k := by
  rw [inverseColumn_correct]
  fin_cases k <;> simp [inertialPlaneInjection, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Transforming a fixed inertial input into RTN coordinates and injecting
it into the inertial variational equation cancels the moving frame exactly. -/
theorem planeInjection_unrotate {z : Fin 5 → ℝ} (hz : PlanarAttitudeFrame.unit z) (q : Vec3) :
    planeInjection z *ᵥ ![(polynomialFrame z |>.transpose |>.mulVec q) 0,
      (polynomialFrame z |>.transpose |>.mulVec q) 1] = PlanarChaserError.planeInput q := by
  dsimp [PlanarAttitudeFrame.unit] at hz
  ext i
  fin_cases i <;>
    simp [planeInjection, polynomialFrame, PlanarChaserError.planeInput,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three]
  · linear_combination (q 0)*hz
  · linear_combination (q 1)*hz

end GNC.PolynomialOrbitTransition
