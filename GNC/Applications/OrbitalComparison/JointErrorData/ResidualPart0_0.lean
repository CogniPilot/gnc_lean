import GNC.Analysis.AffineProductCertificate
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualInputs
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCube

/-! Generated residual check. Identities are exact rational kernel checks;
the complete scalar radius constraint and physical closure are separate. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial BallPolynomialEnclosure DegreeProductCertificate


def residualPart0_0 : Coefficients := []

theorem residualPart0_0_checked : zero (subtract
    (add (basePieces0 0) (scale modelInput.K
      (degreeProduct 0 cubeDeviation coupledPartition0))) residualPart0_0) := by
  decide +kernel

end GNC.OrbitalComparison.JointErrorData
