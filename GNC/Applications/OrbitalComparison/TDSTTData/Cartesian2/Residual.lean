import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree0
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree1
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree2
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree3
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree4
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree5
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree6
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree7
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree8
import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.ResidualDegree9

/-! Generated exact Cartesian checking records. These are ingredients of
the full-field certificate, not assumptions about a numerical ODE solver. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace GNC.OrbitalComparison.TDSTTData.Cartesian2
open ParameterPolynomial PointingCapPolynomial LieSTTOutput

open BallPolynomialEnclosure DegreeProductCertificate ExactDegreeProduct


def residualPieces0 : Fin 10 → Coefficients := ![residual0_0,residual0_1,residual0_2,residual0_3,residual0_4,residual0_5,residual0_6,residual0_7,residual0_8,residual0_9]
theorem residualPieces0_checked : ∀ d, zero (subtract
    (add (basePieces0 d) (scale (3*physicalInput.K)
      (degreeProduct d.val (partition offsetPieces) (partition referencePieces0)))) (residualPieces0 d)) :=
  by
  intro d
  fin_cases d
  · exact residual0_0_checked
  · exact residual0_1_checked
  · exact residual0_2_checked
  · exact residual0_3_checked
  · exact residual0_4_checked
  · exact residual0_5_checked
  · exact residual0_6_checked
  · exact residual0_7_checked
  · exact residual0_8_checked
  · exact residual0_9_checked

theorem residual_component0 (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble residualPieces0) x t=
      value (CartesianReducedPolynomial.residual physicalInput 0) x t := by
  have h := checked_affine 9 (partition offsetPieces) (partition referencePieces0)
    (3*physicalInput.K) (by
      intro i j
      have hi := i.isLt
      have hj := j.isLt
      simp only [partition] at hi hj
      change i.val+j.val≤9
      omega) basePieces0 residualPieces0 residualPieces0_checked x t
  rw [partition_value,partition_value,offsetPieces_value,referencePieces0_value,
    ←ParameterPolynomial.identity _ _ basePieces0_checked x t] at h
  rw [CartesianReducedPolynomial.residual,value_add,value_scale,value_multiply]
  simpa only [mul_assoc] using h

def residualPieces1 : Fin 10 → Coefficients := ![residual1_0,residual1_1,residual1_2,residual1_3,residual1_4,residual1_5,residual1_6,residual1_7,residual1_8,residual1_9]
theorem residualPieces1_checked : ∀ d, zero (subtract
    (add (basePieces1 d) (scale (3*physicalInput.K)
      (degreeProduct d.val (partition offsetPieces) (partition referencePieces1)))) (residualPieces1 d)) :=
  by
  intro d
  fin_cases d
  · exact residual1_0_checked
  · exact residual1_1_checked
  · exact residual1_2_checked
  · exact residual1_3_checked
  · exact residual1_4_checked
  · exact residual1_5_checked
  · exact residual1_6_checked
  · exact residual1_7_checked
  · exact residual1_8_checked
  · exact residual1_9_checked

theorem residual_component1 (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble residualPieces1) x t=
      value (CartesianReducedPolynomial.residual physicalInput 1) x t := by
  have h := checked_affine 9 (partition offsetPieces) (partition referencePieces1)
    (3*physicalInput.K) (by
      intro i j
      have hi := i.isLt
      have hj := j.isLt
      simp only [partition] at hi hj
      change i.val+j.val≤9
      omega) basePieces1 residualPieces1 residualPieces1_checked x t
  rw [partition_value,partition_value,offsetPieces_value,referencePieces1_value,
    ←ParameterPolynomial.identity _ _ basePieces1_checked x t] at h
  rw [CartesianReducedPolynomial.residual,value_add,value_scale,value_multiply]
  simpa only [mul_assoc] using h

def residualPieces2 : Fin 10 → Coefficients := ![residual2_0,residual2_1,residual2_2,residual2_3,residual2_4,residual2_5,residual2_6,residual2_7,residual2_8,residual2_9]
theorem residualPieces2_checked : ∀ d, zero (subtract
    (add (basePieces2 d) (scale (3*physicalInput.K)
      (degreeProduct d.val (partition offsetPieces) (partition referencePieces2)))) (residualPieces2 d)) :=
  by
  intro d
  fin_cases d
  · exact residual2_0_checked
  · exact residual2_1_checked
  · exact residual2_2_checked
  · exact residual2_3_checked
  · exact residual2_4_checked
  · exact residual2_5_checked
  · exact residual2_6_checked
  · exact residual2_7_checked
  · exact residual2_8_checked
  · exact residual2_9_checked

theorem residual_component2 (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble residualPieces2) x t=
      value (CartesianReducedPolynomial.residual physicalInput 2) x t := by
  have h := checked_affine 9 (partition offsetPieces) (partition referencePieces2)
    (3*physicalInput.K) (by
      intro i j
      have hi := i.isLt
      have hj := j.isLt
      simp only [partition] at hi hj
      change i.val+j.val≤9
      omega) basePieces2 residualPieces2 residualPieces2_checked x t
  rw [partition_value,partition_value,offsetPieces_value,referencePieces2_value,
    ←ParameterPolynomial.identity _ _ basePieces2_checked x t] at h
  rw [CartesianReducedPolynomial.residual,value_add,value_scale,value_multiply]
  simpa only [mul_assoc] using h

def residualDegrees : Fin 10 → DiskPolynomial.Vector 3 := ![residualDegree0,residualDegree1,residualDegree2,residualDegree3,residualDegree4,residualDegree5,residualDegree6,residualDegree7,residualDegree8,residualDegree9]
def residualRanges : Fin 10 → DiskTimePolynomial.Certificate 3 := ![residual0Range,residual1Range,residual2Range,residual3Range,residual4Range,residual5Range,residual6Range,residual7Range,residual8Range,residual9Range]
def residual : PointingCapPolynomial.Vector := fun i => assemble (fun d => residualDegrees d i)
def residualBound : List ℚ := profileSum fun d => (residualRanges d).bound 1
theorem residual_value (x : Fin 3 → ℝ) (t : ℝ) :
    value3 residual x t=value3 (CartesianReducedPolynomial.residual physicalInput) x t := by
  ext i
  fin_cases i
  · exact residual_component0 x t
  · exact residual_component1 x t
  · exact residual_component2 x t

theorem residual_ranges_checked : ∀ d,
    BallNormProfile.CertificateValid (residualRanges d) (residualDegrees d) (1/10) := by
  intro d
  fin_cases d
  · exact residual0_range_checked
  · exact residual1_range_checked
  · exact residual2_range_checked
  · exact residual3_range_checked
  · exact residual4_range_checked
  · exact residual5_range_checked
  · exact residual6_range_checked
  · exact residual7_range_checked
  · exact residual8_range_checked
  · exact residual9_range_checked

theorem residual_range_bound {x : Fin 3 → ℝ} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤((1/10:ℚ):ℝ)^2) (ht : 0≤t) :
    ‖DiskPolynomial.vectorValue residual x t‖≤PolynomialOrder.value residualBound t :=
  DegreeVectorCertificate.vector_sum_bound residualDegrees residualRanges residual_ranges_checked hx ht

end GNC.OrbitalComparison.TDSTTData.Cartesian2
