import GNC.Applications.OrbitalFuel.TerminalData
import GNC.Applications.OrbitalFuel.TargetThrustData

/-! Polynomial terminal RTN free-response expressions in physical units.
Inputs 0--24 are the terminal reference/transition state; 25 is the SI speed
unit, 26 the initial normalized speed, and 27--30 the target-thrust pullback.
-/
namespace GNC.Applications.OrbitalFuel.FreeResponse
open GNC.PolynomialODE

def lengthUnit : ℚ := 149597870700
def alpha : ℚ := PolynomialTransition.alpha

def center (i : Fin 31) : ℚ :=
  if h : i.val < 25 then TerminalData.endpoint ⟨i.val,h⟩
  else if i.val = 25 then TerminalData.speedCenter
  else if i.val = 26 then TerminalData.initialSpeedCenter
  else TargetThrust.centers ⟨i.val-27,by omega⟩

def allowance (i : Fin 31) : ℚ :=
  if i.val < 5 then 1/10^19
  else if i.val < 25 then 1/10^16
  else if i.val < 27 then 1/10^25 else 1/10^14

def region (i : Fin 31) : ℚ := |center i|+allowance i

def sum4 (f : Fin 4 → Expr 31) : Expr 31 :=
  ((f 0).add (f 1)).add ((f 2).add (f 3))

def frameEntry (i j : Fin 2) : Expr 31 :=
  let x := (Expr.var 0).multiply (Expr.var 4)
  let y := (Expr.var 1).multiply (Expr.var 4)
  ![![x,y],![y.negate,x]] i j

def planeEntry (i j : Fin 4) : Expr 31 := Expr.var ⟨5+4*i.val+j.val,by omega⟩
def normalEntry (i j : Fin 2) : Expr 31 := Expr.var ⟨21+2*i.val+j.val,by omega⟩

/-- Zero rotating velocity gives a nonzero inertial velocity correction. -/
def initialPlane (i : Fin 4) : Expr 31 :=
  ![Expr.constant 0, Expr.constant (-10000000/lengthUnit),
    (Expr.constant (12500000/lengthUnit)).multiply (Expr.var 26), Expr.constant 0] i

def pulledPlane (i : Fin 4) : Expr 31 :=
  (initialPlane i).add (((Expr.constant alpha).multiply (Expr.var ⟨27+i.val,by omega⟩)).negate)

def planeValue (i : Fin 4) : Expr 31 :=
  sum4 (fun j => (planeEntry i j).multiply (pulledPlane j))

def normalValue (i : Fin 2) : Expr 31 :=
  (normalEntry i 0).multiply (Expr.constant (1000000/lengthUnit))

def normalizedOutput (i : Fin 6) : Expr 31 :=
  if h : i.val%3 < 2 then
    let r : Fin 2 := ⟨i.val%3,h⟩
    let j : Fin 4 := ⟨2*(i.val/3),by omega⟩
    let k : Fin 4 := ⟨2*(i.val/3)+1,by omega⟩
    ((frameEntry r 0).multiply (planeValue j)).add ((frameEntry r 1).multiply (planeValue k))
  else normalValue ⟨i.val/3,by omega⟩

def output (i : Fin 6) : Expr 31 :=
  (if i.val < 3 then Expr.constant lengthUnit else Expr.var 25).multiply (normalizedOutput i)

def tolerance (i : Fin 6) : ℚ := if i.val < 3 then 150000 else 1/10

def constraintOutput (i : Fin 6) : Expr 31 :=
  (Expr.constant (1/tolerance i)).multiply (output i)

theorem allowance_nonneg (i : Fin 31) : 0 ≤ allowance i := by
  unfold allowance
  split_ifs <;> norm_num

theorem region_nonneg (i : Fin 31) : 0 ≤ region i :=
  add_nonneg (abs_nonneg _) (allowance_nonneg i)

end GNC.Applications.OrbitalFuel.FreeResponse
