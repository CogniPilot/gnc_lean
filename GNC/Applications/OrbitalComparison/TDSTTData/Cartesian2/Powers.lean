import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Cube0
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Cube1
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Cube2
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Cube3
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Cube4
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Cube5
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Cube6

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def cubePieces : Fin 7 → Coefficients := ![cube0,cube1,cube2,cube3,cube4,cube5,cube6]
theorem cubePieces_checked : ∀ d, zero (subtract
    (degreeProduct d.val (partition squarePieces) (partition oneOffsetPieces)) (cubePieces d)) :=
  by
  intro d
  fin_cases d
  · exact cube0_checked
  · exact cube1_checked
  · exact cube2_checked
  · exact cube3_checked
  · exact cube4_checked
  · exact cube5_checked
  · exact cube6_checked


def offsetCube : Coefficients := assemble cubePieces
theorem offsetCube_value (x : Fin 3 → ℝ) (t : ℝ) :
    value offsetCube x t=(1+value inverseOffset x t)^3 := by
  have h := checked_product 6 (partition squarePieces) (partition oneOffsetPieces)
    (by intro i j; have hi := i.isLt; have hj := j.isLt
        simp only [partition] at hi hj
        change i.val+j.val≤6; omega) cubePieces cubePieces_checked x t
  rw [partition_value,partition_value,oneOffsetPieces_value] at h
  change value offsetCube x t=value offsetSquare x t*(1+value inverseOffset x t) at h
  rw [offsetSquare_value] at h
  exact h.trans (by ring)

end GNC.OrbitalComparison.TDSTTData.Cartesian2
