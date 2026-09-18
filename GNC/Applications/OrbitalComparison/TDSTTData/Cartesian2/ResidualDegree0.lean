import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ReducedInputs

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def residual0_0 : Coefficients := []
theorem residual0_0_checked : zero (subtract
    (add (basePieces0 0) (scale (3*physicalInput.K)
      (degreeProduct 0 (partition offsetPieces) (partition referencePieces0)))) residual0_0) := by
  decide +kernel

def residual1_0 : Coefficients := []
theorem residual1_0_checked : zero (subtract
    (add (basePieces1 0) (scale (3*physicalInput.K)
      (degreeProduct 0 (partition offsetPieces) (partition referencePieces1)))) residual1_0) := by
  decide +kernel

def residual2_0 : Coefficients := []
theorem residual2_0_checked : zero (subtract
    (add (basePieces2 0) (scale (3*physicalInput.K)
      (degreeProduct 0 (partition offsetPieces) (partition referencePieces2)))) residual2_0) := by
  decide +kernel

def residualDegree0 : PointingCapPolynomial.Vector := ![residual0_0,residual1_0,residual2_0]
def residual0Range : DiskTimePolynomial.Certificate 3 where
  count := 0
  terms := ![]

theorem residual0_range_checked : BallNormProfile.CertificateValid
    residual0Range (residualDegree0) (1/10) := by
  constructor
  · intro k
    fin_cases k <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel


end GNC.OrbitalComparison.TDSTTData.Cartesian2
