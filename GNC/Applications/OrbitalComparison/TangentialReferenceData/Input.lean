import GNC.Dynamics.PolynomialOrbit
import GNC.Analysis.PolynomialChain

namespace GNC.OrbitalComparison.TangentialReferenceData
open PolynomialODE PolynomialOrbit
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def alpha : ℚ := (24500/1993002209)
def stepLength : ℚ := (13/640)
def errorBound : ℚ := (42758279555735360403463/340282366920938463463374607431768211456)
def inverseBound : ℚ := (340282367049446914586991260043052890537/340282366920938463463374607431768211456)
def radialLower : ℚ := (549756419603/549755813888)
def radialUpper : ℚ := (1099512839207/1099511627776)
end GNC.OrbitalComparison.TangentialReferenceData
