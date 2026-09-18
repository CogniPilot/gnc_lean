import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Square

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def cube0 : Coefficients := [⟨0,0,0,[1]⟩]
theorem cube0_checked : zero (subtract
    (degreeProduct 0 (partition squarePieces) (partition oneOffsetPieces)) cube0) := by
  decide +kernel

end GNC.OrbitalComparison.TDSTTData.Cartesian2
