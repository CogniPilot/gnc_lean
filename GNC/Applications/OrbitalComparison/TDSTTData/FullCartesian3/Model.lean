import GNC.Applications.OrbitalComparison.TDSTTData.FullCartesian3.Input
import GNC.Applications.OrbitalComparison.CartesianCubicPolynomial
import GNC.Applications.OrbitalComparison.JointErrorReference

/-! Generated exact Cartesian cubic checking records. The numerical
coefficient solver is untrusted; the physical residual charges its errors. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.FullCartesian3
open ParameterPolynomial PointingCapPolynomial LieSTTOutput Matrix


def physicalInput : JointErrorPolynomial.Input :=
  {JointErrorData.modelInput with rho := position, h := inverseOffset}

end GNC.OrbitalComparison.TDSTTData.FullCartesian3
