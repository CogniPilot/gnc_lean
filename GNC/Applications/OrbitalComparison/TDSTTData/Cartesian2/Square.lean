import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Square0
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Square1
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Square2
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Square3
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Square4

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def squarePieces : Fin 5 → Coefficients := ![square0,square1,square2,square3,square4]
theorem squarePieces_checked : ∀ d, zero (subtract
    (degreeProduct d.val (partition oneOffsetPieces) (partition oneOffsetPieces)) (squarePieces d)) :=
  by
  intro d
  fin_cases d
  · exact square0_checked
  · exact square1_checked
  · exact square2_checked
  · exact square3_checked
  · exact square4_checked


def offsetSquare : Coefficients := assemble squarePieces
theorem offsetSquare_value (x : Fin 3 → ℝ) (t : ℝ) :
    value offsetSquare x t=(1+value inverseOffset x t)^2 := by
  have h := checked_product 4 (partition oneOffsetPieces) (partition oneOffsetPieces)
    (by intro i j; have hi := i.isLt; have hj := j.isLt
        simp only [partition] at hi hj
        change i.val+j.val≤4; omega) squarePieces squarePieces_checked x t
  simp only [partition_value,oneOffsetPieces_value] at h
  exact h.trans (by ring)

end GNC.OrbitalComparison.TDSTTData.Cartesian2
