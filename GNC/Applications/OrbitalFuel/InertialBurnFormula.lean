import GNC.Applications.OrbitalFuel.PolynomialBurns
import GNC.Applications.OrbitalFuel.BurnTheory
import GNC.Dynamics.PlanarInertialBurn

/-! Exact rational burn means for constant inertial directions. The burn
partition and validated joint reference/transition polynomials are reused. -/
namespace GNC.Applications.OrbitalFuel.InertialBurn
open GNC.PolynomialODE GNC.PolynomialOrbitTransition PolynomialTransition

def observable (o : Fin 10) : Expr 25 :=
  if h : o.val < 8 then inverseColumn ⟨o.val/2,by omega⟩ ⟨o.val%2,by omega⟩
  else normalObservable ⟨o.val-8,by omega⟩

def mean (j : Fin 18) (o : Fin 10) : ℚ :=
  PolynomialBurn.observationMean (PolynomialBurn.cells j) (observable o)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem observation_errors (j : Fin 32) (o : Fin 10) :
    (observable o).differenceMajorant (steps j).region (steps j).error ≤ 1/10^14 := by
  revert j o
  decide +kernel

end GNC.Applications.OrbitalFuel.InertialBurn
