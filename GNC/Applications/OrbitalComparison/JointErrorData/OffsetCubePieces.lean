import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart0
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart1
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart2
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart3
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart4
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart5
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart6
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart7
import GNC.Applications.OrbitalComparison.JointErrorData.OffsetCubePart8

namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial

def offsetCubePieces : Fin 9 → Coefficients := ![offsetCubePart0, offsetCubePart1, offsetCubePart2, offsetCubePart3, offsetCubePart4, offsetCubePart5, offsetCubePart6, offsetCubePart7, offsetCubePart8]

theorem offsetCubePieces_checked : ∀ d, zero (subtract
    (DegreeProductCertificate.degreeProduct d.val offsetSquare oneOffset)
    (offsetCubePieces d)) := by
  intro d
  fin_cases d
  · exact offsetCubePart0_checked
  · exact offsetCubePart1_checked
  · exact offsetCubePart2_checked
  · exact offsetCubePart3_checked
  · exact offsetCubePart4_checked
  · exact offsetCubePart5_checked
  · exact offsetCubePart6_checked
  · exact offsetCubePart7_checked
  · exact offsetCubePart8_checked

end GNC.OrbitalComparison.JointErrorData
