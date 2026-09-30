import GNC.Dynamics.PlanarChaserError
import GNC.Analysis.PolynomialStepObservable

/-! Polynomial observables of the exact inverse-radius lift. These are the
physical gravity gradient and tangential reference thrust, not derivatives
of an approximate ephemeris. Observable transfer charges ephemeris error.+-/
namespace GNC.PolynomialGravityObservable
open PolynomialODE PolynomialOrbit PolynomialOrbitTransition

def gradient (i j : Fin 3) : Expr 5 :=
  let x := Expr.var 0
  let y := Expr.var 1
  let u := Expr.var 4
  let u3 := u.multiply (u.multiply u)
  let u5 := u3.multiply (u.multiply u)
  let xx := ((Expr.constant 3).multiply (u5.multiply (x.multiply x))).add u3.negate
  let xy := (Expr.constant 3).multiply (u5.multiply (x.multiply y))
  let yy := ((Expr.constant 3).multiply (u5.multiply (y.multiply y))).add u3.negate
  !![xx,xy,Expr.constant 0; xy,yy,Expr.constant 0;
    Expr.constant 0,Expr.constant 0,u3.negate] i j

def thrust (a : ℚ) (i : Fin 3) : Expr 5 :=
  ![((Expr.constant (-a)).multiply ((Expr.var 4).multiply (Expr.var 1))),
    ((Expr.constant a).multiply ((Expr.var 4).multiply (Expr.var 0))),
    Expr.constant 0] i

/-- Every radial/tangential/normal force column, including out-of-plane
forcing. The normal column is constant; its exact slope is zero. -/
def frameInput (a : ℚ) (i j : Fin 3) : Expr 5 :=
  let xu := (Expr.var 0).multiply (Expr.var 4)
  let yu := (Expr.var 1).multiply (Expr.var 4)
  (Expr.constant a).multiply
    (!![xu,yu.negate,Expr.constant 0; yu,xu,Expr.constant 0;
      Expr.constant 0,Expr.constant 0,Expr.constant 1] i j)

theorem frameInput_value (a : ℚ) (z : Fin 5 → ℝ) (i j : Fin 3) :
    (frameInput a i j).value z=(a:ℝ)*polynomialFrame z i j := by
  fin_cases i <;> fin_cases j <;>
    simp [frameInput,Expr.value,polynomialFrame,Matrix.cons_val_two] <;> ring

theorem frameInput_slope (a : ℚ) {M : ℚ} (hM : 0≤M) (i j : Fin 3) :
    (frameInput a i j).slope M≤2*|a| *M := by
  fin_cases i <;> fin_cases j <;>
    simp [frameInput,Expr.slope,Expr.majorant,Matrix.cons_val_two] <;>
    nlinarith [abs_nonneg a]

theorem gradient_value (z : Fin 5 → ℝ) (i j : Fin 3) :
    (gradient i j).value z=gravityMatrix z i j := by
  fin_cases i <;> fin_cases j <;>
    simp [gradient,Expr.value,gravityMatrix,Matrix.cons_val_two] <;> ring

theorem thrust_value (a : ℚ) (w : Fin 4 → ℝ) (i : Fin 3) :
    (thrust a i).value (lift w)=PlanarChaserError.referenceThrust (a:ℝ) w i := by
  fin_cases i <;> simp [thrust,Expr.value,PlanarChaserError.referenceThrust,
    polynomialFrame,lift,Matrix.cons_val_two] <;> ring_nf <;> simp

theorem gradient_slope {M : ℚ} (hM : 0≤M) (i j : Fin 3) :
    (gradient i j).slope M≤21*M^6+3*M^2 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [gradient,Expr.slope,Expr.majorant,Matrix.cons_val_two] <;>
    nlinarith [pow_nonneg hM 6, sq_nonneg M]

theorem thrust_slope (a : ℚ) {M : ℚ} (hM : 0≤M) (i : Fin 3) :
    (thrust a i).slope M≤2*|a| *M := by
  fin_cases i <;> simp [thrust,Expr.slope,Expr.majorant] <;>
    nlinarith [abs_nonneg a]

end GNC.PolynomialGravityObservable
