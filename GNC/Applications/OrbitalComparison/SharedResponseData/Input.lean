import GNC.Applications.OrbitalComparison.TangentialReferenceObservables
import GNC.Analysis.AffinePolynomialChain

namespace GNC.OrbitalComparison.SharedResponseData
open GNC.AffinePolynomialStep
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def geometricOperator (cs : Fin 5 → List ℚ) : Fin 8 → Fin 8 → List ℚ :=
  let g := fun i j => (GNC.PolynomialGravityObservable.gradient i j).coefficients cs
  !![[],[],[],[],[1],[],[],[];
    [],[],[],[],[],[1],[],[];
    [],[],[],[],[],[],[1],[];
    [],[],[],[],[],[],[],[1];
    g 0 0,g 0 1,[],[],[],[],[],[];
    g 1 0,g 1 1,[],[],[],[],[],[];
    [],[],g 2 2,[],[],[],[],[];
    [],[],[],g 2 2,[],[],[],[]]
def geometricInput (cs : Fin 5 → List ℚ) : Fin 8 → List ℚ :=
  let e := fun k => GNC.PolynomialGravityObservable.frameInput TangentialReferenceData.alpha k 1
  let u := fun k => (e k).coefficients cs
  let v := fun k => (e k).negate.coefficients cs
  ![[],[],[],[],v 1,u 0,u 1,v 0]
def geometricError : ℚ := (35847271355958079329379377407/170141183460469231731687303715884105728)

def cartesianOperator (cs : Fin 5 → List ℚ) : Fin 20 → Fin 20 → List ℚ :=
  let g := fun i j => (GNC.PolynomialGravityObservable.gradient i j).coefficients cs
  !![[],[],[],[],[],[],[],[],[],[],[1],[],[],[],[],[],[],[],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[1],[],[],[],[],[],[],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[1],[],[],[],[],[],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[],[1],[],[],[],[],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[1],[],[],[],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1],[],[],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1],[],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1],[],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1],[];
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[1];
    g 0 0,g 0 1,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[];
    g 1 0,g 1 1,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[];
    [],[],g 0 0,g 0 1,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[];
    [],[],g 1 0,g 1 1,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[];
    [],[],[],[],g 0 0,g 0 1,[],[],[],[],[],[],[],[],[],[],[],[],[],[];
    [],[],[],[],g 1 0,g 1 1,[],[],[],[],[],[],[],[],[],[],[],[],[],[];
    [],[],[],[],[],[],g 0 0,g 0 1,[],[],[],[],[],[],[],[],[],[],[],[];
    [],[],[],[],[],[],g 1 0,g 1 1,[],[],[],[],[],[],[],[],[],[],[],[];
    [],[],[],[],[],[],[],[],g 2 2,[],[],[],[],[],[],[],[],[],[],[];
    [],[],[],[],[],[],[],[],[],g 2 2,[],[],[],[],[],[],[],[],[],[]]
def cartesianInput (cs : Fin 5 → List ℚ) : Fin 20 → List ℚ :=
  let e := fun k => GNC.PolynomialGravityObservable.frameInput TangentialReferenceData.alpha k 1
  let u := fun k => (e k).coefficients cs
  let v := fun k => (e k).negate.coefficients cs
  ![[],[],[],[],[],[],[],[],[],[],u 0,[],u 1,[],[],u 0,[],u 1,u 0,u 1]
def cartesianError : ℚ := (98133948965772457694458532847/340282366920938463463374607431768211456)

end GNC.OrbitalComparison.SharedResponseData
