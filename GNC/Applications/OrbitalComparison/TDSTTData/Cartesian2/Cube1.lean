import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Square

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def cube1 : Coefficients := [⟨0,0,1,[0,0,(4427218577690307/590295810358705651712),(-4770914720935311/1180591620717411303424),(36904650520887/1180591620717411303424),(3976964737635/1180591620717411303424),(-20006491017/1180591620717411303424),(-1555359/1152921504606846976),(3648045/590295810358705651712)]⟩]
theorem cube1_checked : zero (subtract
    (degreeProduct 1 (partition squarePieces) (partition oneOffsetPieces)) cube1) := by
  decide +kernel

end GNC.OrbitalComparison.TDSTTData.Cartesian2
