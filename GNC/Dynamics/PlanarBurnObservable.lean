import GNC.Dynamics.PlanarThrustFrame
import GNC.Analysis.PolynomialObservable

/-! Polynomial form of the pullback of a physical RTN burn direction.
The inverse fundamental matrices are supplied by the symplectic identity.
-/
namespace GNC.PolynomialOrbitTransition
open PolynomialODE Matrix
open scoped Matrix

def inverseColumn (i : Fin 4) (k : Fin 2) : Expr 25 :=
  let r : Fin 4 := k.castLE (by decide)
  ![(Expr.var (planeIndex r 2)).negate, (Expr.var (planeIndex r 3)).negate,
    Expr.var (planeIndex r 0), Expr.var (planeIndex r 1)] i

def planeObservable (i : Fin 4) (j : Fin 2) : Expr 25 :=
  let x := (Expr.var 0).multiply (Expr.var 4)
  let y := (Expr.var 1).multiply (Expr.var 4)
  ((inverseColumn i 0).multiply (![x,y.negate] j)).add
    ((inverseColumn i 1).multiply (![y,x] j))

def normalObservable (i : Fin 2) : Expr 25 :=
  ![(Expr.var (normalIndex 0 1)).negate, Expr.var (normalIndex 0 0)] i

noncomputable def planeInjection (z : Fin 5 → ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![0,0; 0,0; z 0*z 4,-z 1*z 4; z 1*z 4,z 0*z 4]

noncomputable def physicalPlaneInjection (w : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![0,0; 0,0; physicalFrame w 0 0,physicalFrame w 0 1;
    physicalFrame w 1 0,physicalFrame w 1 1]

theorem planeInjection_physical (w : Fin 4 → ℝ) (hh : 0 < angularMomentum w) :
    planeInjection (GNC.PolynomialOrbit.lift w) = physicalPlaneInjection w := by
  simp [physicalPlaneInjection, physicalFrame_eq w hh, polynomialFrame, planeInjection]

set_option maxHeartbeats 2000000 in
theorem planeObservable_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 4) (j : Fin 2) :
    (planeObservable i j).value (pack z F H) = (planeInverse F * planeInjection z) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [planeObservable, inverseColumn, Expr.value, planeInverse, planeForm,
      planeInjection, pack, planeIndex, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ, cons_val_two, cons_val_three, cons_val_four] <;>
    ring_nf <;> simp <;> ring

theorem normalObservable_correct (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    (normalObservable i).value (pack z F H) = normalInverse H i 1 := by
  fin_cases i <;>
    simp [normalObservable, Expr.value, normalInverse, normalForm, pack, normalIndex,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

end GNC.PolynomialOrbitTransition
