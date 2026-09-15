import GNC.Applications.OrbitalFuel.FreeResponseFormula
import GNC.Applications.OrbitalFuel.PolynomialBurns

/-! Terminal sensitivity expressions for one normalized solar burn. The first
31 inputs retain the free-response layout; the last ten are that burn's
pullback means. All scales and commanded attitude entries are exact rationals,
except the SI speed, which is a separately enclosed input. -/
namespace GNC.Applications.OrbitalFuel.BurnSensitivity
open GNC.PolynomialODE

def embed (i : Fin 31) : Fin 41 := ⟨i.val,by omega⟩
def lift (e : Expr 31) : Expr 41 := e.rename embed
def meanSlot (i : Fin 10) : Fin 41 := ⟨31+i.val,by omega⟩

def center (j : Fin 18) (i : Fin 41) : ℚ :=
  if h : i.val < 31 then FreeResponse.center ⟨i.val,h⟩
  else PolynomialBurn.centers j ⟨i.val-31,by omega⟩

def allowance (i : Fin 41) : ℚ :=
  if h : i.val < 31 then FreeResponse.allowance ⟨i.val,h⟩ else 2/10^14

def region (j : Fin 18) (i : Fin 41) : ℚ := |center j i|+allowance i

/-- Maximum normalized acceleration times the common normalized burn duration. -/
def burnScale : ℚ := FreeResponse.lengthUnit^2/(132712440018000000000*10000*50)

def base : Fin 6 → Matrix (Fin 3) (Fin 3) ℚ :=
  ![!![0,0,1; 1,0,0; 0,1,0], !![1,0,0; 0,0,1; 0,-1,0],
    !![1,0,0; 0,1,0; 0,0,1], !![0,0,-1; 1,0,0; 0,-1,0],
    !![1,0,0; 0,0,-1; 0,1,0], !![1,0,0; 0,-1,0; 0,0,-1]]

def rotation (j : Fin 18) (r c : Fin 3) : ℚ :=
  base ⟨j.val%6,Nat.mod_lt _ (by norm_num)⟩ r c *
    if j.val/6%2 = 1 ∧ c.val < 2 then -1 else 1

def planeMean (i : Fin 4) (k : Fin 2) : Expr 41 :=
  Expr.var (meanSlot ⟨2*i.val+k.val,by omega⟩)

def normalMean (i : Fin 2) : Expr 41 := Expr.var (meanSlot ⟨8+i.val,by omega⟩)

def planeValue (i : Fin 4) (k : Fin 2) : Expr 41 :=
  (((lift (FreeResponse.planeEntry i 0)).multiply (planeMean 0 k)).add
    ((lift (FreeResponse.planeEntry i 1)).multiply (planeMean 1 k))).add
  (((lift (FreeResponse.planeEntry i 2)).multiply (planeMean 2 k)).add
    ((lift (FreeResponse.planeEntry i 3)).multiply (planeMean 3 k)))

def normalValue (i : Fin 2) : Expr 41 :=
  ((lift (FreeResponse.normalEntry i 0)).multiply (normalMean 0)).add
    ((lift (FreeResponse.normalEntry i 1)).multiply (normalMean 1))

def normalizedEntry (i : Fin 6) (k : Fin 3) : Expr 41 :=
  if hr : i.val%3 < 2 then
    if hk : k.val < 2 then
      let r : Fin 2 := ⟨i.val%3,hr⟩
      let c : Fin 2 := ⟨k.val,hk⟩
      ((lift (FreeResponse.frameEntry r 0)).multiply (planeValue ⟨2*(i.val/3),by omega⟩ c)).add
        ((lift (FreeResponse.frameEntry r 1)).multiply (planeValue ⟨2*(i.val/3)+1,by omega⟩ c))
    else Expr.constant 0
  else if k.val = 2 then normalValue ⟨i.val/3,by omega⟩ else Expr.constant 0

def outputEntry (i : Fin 6) (k : Fin 3) : Expr 41 :=
  (Expr.constant (burnScale/FreeResponse.tolerance i)).multiply
    ((if i.val < 3 then Expr.constant FreeResponse.lengthUnit else Expr.var 25).multiply
      (normalizedEntry i k))

def coefficient (i : Fin 12) (j : Fin 18) (k : Fin 3) : Expr 41 :=
  let r : Fin 6 := ⟨i.val/2,by omega⟩
  (Expr.constant (if i.val%2 = 0 then -1 else 1)).multiply
    ((((outputEntry r 0).multiply (Expr.constant (rotation j 0 k))).add
      ((outputEntry r 1).multiply (Expr.constant (rotation j 1 k)))).add
      ((outputEntry r 2).multiply (Expr.constant (rotation j 2 k))))

theorem allowance_nonneg (i : Fin 41) : 0 ≤ allowance i := by
  unfold allowance
  split_ifs
  · exact FreeResponse.allowance_nonneg _
  · norm_num

theorem region_nonneg (j : Fin 18) (i : Fin 41) : 0 ≤ region j i :=
  add_nonneg (abs_nonneg _) (allowance_nonneg i)

end GNC.Applications.OrbitalFuel.BurnSensitivity
