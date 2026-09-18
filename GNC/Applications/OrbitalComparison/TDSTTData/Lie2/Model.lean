import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Input
import GNC.Applications.OrbitalComparison.LieReducedPolynomial
import GNC.Applications.OrbitalComparison.JointErrorReference

/-! Generated exact Lie checking records; no numerical solver is trusted. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Lie2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput BallPolynomialEnclosure


def physicalInput : JointErrorPolynomial.Input :=
  { JointErrorData.modelInput with rho := position, h := inverseOffset }

end GNC.OrbitalComparison.TDSTTData.Lie2
