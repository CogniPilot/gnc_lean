import GNC.Applications.OrbitalFuel.BurnFormula

/-! Whole-horizon pullback of the target's prescribed tangential thrust.
These integrals enter the affine relative-motion response with a minus sign.
They differ from the chaser's eighteen short burn means.
-/
namespace GNC.Applications.OrbitalFuel.TargetThrust
open PolynomialBurn

def fullCell (k : Fin 32) : Cell := ⟨k,0,3/160⟩
def tangentSlot (i : Fin 4) : Fin 10 := ⟨2*i.val+1,by omega⟩
def integralSum (i : Fin 4) : ℚ := ∑ k : Fin 32, cellIntegral (fullCell k) (tangentSlot i)

theorem fullCell_valid (k : Fin 32) : (fullCell k).Valid := by
  norm_num [fullCell, Cell.Valid]

end GNC.Applications.OrbitalFuel.TargetThrust
