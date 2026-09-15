import GNC.Applications.OrbitalFuel.TargetThrustFormula

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace GNC.Applications.OrbitalFuel.TargetThrust

def centers : Fin 4 → ℚ := ![(12814634610860299282032620409/125000000000000000000000000000), (-135286186613802480621348039011/1000000000000000000000000000000), (-74167944228290727642208107729/250000000000000000000000000000), (228190970748479471274648264469/500000000000000000000000000000)]

theorem centers_error : ∀ i, |integralSum i-centers i| ≤ 1/10^25 := by decide +kernel

end GNC.Applications.OrbitalFuel.TargetThrust
