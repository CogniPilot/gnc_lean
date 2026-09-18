import GNC.Applications.OrbitalComparison.JointErrorData.ResidualPart0_0
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualPart1_0
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualPart2_0

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial

def residualDegree0 : DiskPolynomial.Vector 3 := ![residualPart0_0,residualPart1_0,residualPart2_0]
def residualRange0 : DiskTimePolynomial.Certificate 3 where
  count := 0
  terms := ![]

theorem residualRange0_checked : BallNormProfile.CertificateValid residualRange0 residualDegree0 (mkRat (1) 10) := by
  constructor
  · intro k
    fin_cases k <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

end GNC.OrbitalComparison.JointErrorData
