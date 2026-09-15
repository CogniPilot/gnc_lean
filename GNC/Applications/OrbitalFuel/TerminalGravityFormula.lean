import GNC.Applications.OrbitalFuel.ValidatedTerminalData
import GNC.Analysis.PolynomialNormIntegral

/-! Terminal RTN rows of the acceleration-to-error transition.
Inputs 0--24 are the terminal reference/transition entries, and 25--49
are the entries at the forcing time. Both sets retain their certified
uncertainty. Squaring a row gives a polynomial observable whose integral
can be evaluated exactly and converted to a norm-integral upper bound.
-/
namespace GNC.Applications.OrbitalFuel.TerminalGravity
open GNC.PolynomialODE GNC.PolynomialIntegral PolynomialTransition

def sum4 (f : Fin 4 → Expr 50) : Expr 50 :=
  ((f 0).add (f 1)).add ((f 2).add (f 3))

def frame (r k : Fin 2) : Expr 50 :=
  let x := (Expr.var 0).multiply (Expr.var 4)
  let y := (Expr.var 1).multiply (Expr.var 4)
  ![![x,y],![y.negate,x]] r k

def finalPlane (r j : Fin 4) : Expr 50 := .var ⟨5+4*r.val+j.val,by omega⟩

/-- Last two columns of the symplectic inverse, without numerical inversion. -/
def inversePlaneInput (j : Fin 4) (k : Fin 2) : Expr 50 :=
  if h : j.val < 2 then (Expr.var ⟨30+4*k.val+j.val+2,by omega⟩).negate
  else Expr.var ⟨30+4*k.val+(j.val-2),by omega⟩

def planeRow (i : Fin 6) (r : Fin 2) (j : Fin 4) : Expr 50 :=
  ((frame r 0).multiply (finalPlane ⟨2*(i.val/3),by omega⟩ j)).add
    ((frame r 1).multiply (finalPlane ⟨2*(i.val/3)+1,by omega⟩ j))

def rowEntry (i : Fin 6) (k : Fin 3) : Expr 50 :=
  if hr : i.val%3 < 2 then
    if hk : k.val < 2 then
      sum4 (fun j => (planeRow i ⟨i.val%3,hr⟩ j).multiply
        (inversePlaneInput j ⟨k.val,hk⟩))
    else .constant 0
  else if k.val = 2 then
    ((Expr.var ⟨21+2*(i.val/3),by omega⟩).multiply (Expr.var 47).negate).add
      ((Expr.var ⟨22+2*(i.val/3),by omega⟩).multiply (Expr.var 46))
  else .constant 0

def squaredRow (i : Fin 6) : Expr 50 :=
  let square := fun k => (rowEntry i k).multiply (rowEntry i k)
  ((square 0).add (square 1)).add (square 2)

def coefficients (j : Fin 32) (i : Fin 50) : List ℚ :=
  if h : i.val < 25 then [TerminalData.endpoint ⟨i.val,h⟩]
  else (steps j).coefficients ⟨i.val-25,by omega⟩

def allowance (j : Fin 32) (i : Fin 50) : ℚ :=
  if h : i.val < 25 then TerminalData.endpointError ⟨i.val,h⟩
  else (steps j).error ⟨i.val-25,by omega⟩

def region (j : Fin 32) (i : Fin 50) : ℚ :=
  if h : i.val < 25 then |TerminalData.endpoint ⟨i.val,h⟩|+TerminalData.endpointError ⟨i.val,h⟩
  else (steps j).region ⟨i.val-25,by omega⟩

def squaredError : ℚ := 1/10^10

def youngIntegral (j : Fin 32) (i : Fin 6) (ν : ℚ) : ℚ :=
  (integrate ((squaredRow i).coefficients (coefficients j)) 0 (3/160)+
    (3/160)*(ν^2+squaredError))/(2*ν)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem squared_errors : ∀ j i,
    (squaredRow i).differenceMajorant (region j) (allowance j) ≤ squaredError := by
  decide +kernel

end GNC.Applications.OrbitalFuel.TerminalGravity
