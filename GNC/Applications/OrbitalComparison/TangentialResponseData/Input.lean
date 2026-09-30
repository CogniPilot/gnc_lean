import GNC.Applications.OrbitalComparison.TangentialReferenceObservables
import GNC.Analysis.AffinePolynomialChain

namespace GNC.OrbitalComparison.TangentialResponseData
open GNC.AffinePolynomialStep
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def operator (cs : Fin 5 → List ℚ) : Fin 6 → Fin 6 → List ℚ :=
  let g := fun i j => (GNC.PolynomialGravityObservable.gradient i j).coefficients cs
  !![[],[],[],[1],[],[]; [],[],[],[],[1],[]; [],[],[],[],[],[1];
    g 0 0,g 0 1,g 0 2,[],[],[]; g 1 0,g 1 1,g 1 2,[],[],[];
    g 2 0,g 2 1,g 2 2,[],[],[]]
def input (cs : Fin 5 → List ℚ) (i : Fin 3) : Fin 6 → List ℚ :=
  let f := fun k => (GNC.PolynomialGravityObservable.frameInput
    TangentialReferenceData.alpha k i).coefficients cs
  ![[],[],[],f 0,f 1,f 2]
def errorBound : ℚ := (46437083213613181293/340282366920938463463374607431768211456)
end GNC.OrbitalComparison.TangentialResponseData
