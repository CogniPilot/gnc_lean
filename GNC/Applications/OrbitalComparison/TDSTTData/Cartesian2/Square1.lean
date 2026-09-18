import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.PowerInputs

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def square1 : Coefficients := [⟨0,0,1,[0,0,(1475739525896769/295147905179352825856),(-1590304906978437/590295810358705651712),(12301550173629/590295810358705651712),(1325654912545/590295810358705651712),(-6668830339/590295810358705651712),(-518453/576460752303423488),(1216015/295147905179352825856)]⟩]
theorem square1_checked : zero (subtract
    (degreeProduct 1 (partition oneOffsetPieces) (partition oneOffsetPieces)) square1) := by
  decide +kernel

end GNC.OrbitalComparison.TDSTTData.Cartesian2
