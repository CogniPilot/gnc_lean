import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Input
import GNC.Applications.OrbitalComparison.CartesianErrorPolynomial
import GNC.Applications.OrbitalComparison.JointErrorReference

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput


def physicalInput : JointErrorPolynomial.Input :=
  { JointErrorData.modelInput with rho := position, h := inverseOffset }


end GNC.OrbitalComparison.TDSTTData.Cartesian2
