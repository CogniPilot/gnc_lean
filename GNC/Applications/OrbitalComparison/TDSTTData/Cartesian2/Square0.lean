import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.PowerInputs

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def square0 : Coefficients := [⟨0,0,0,[1]⟩]
theorem square0_checked : zero (subtract
    (degreeProduct 0 (partition oneOffsetPieces) (partition oneOffsetPieces)) square0) := by
  decide +kernel

end GNC.OrbitalComparison.TDSTTData.Cartesian2
