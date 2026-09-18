import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange0
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange1
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange2
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange3
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange4
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange5
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange6
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange7
import GNC.Applications.OrbitalComparison.JointErrorData.ResidualRange8
import GNC.Applications.OrbitalComparison.JointResidualCertificate

/-! Complete candidate Lie-residual enclosure on the three-axis ball.
The inverse-radius scalar constraint and physical first-exit theorem are
still required before this becomes a trajectory-error certificate. -/
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial BallPolynomialEnclosure DegreeProductCertificate LieSTTOutput

def residualPolynomials : Fin 9 → DiskPolynomial.Vector 3 := ![residualDegree0,residualDegree1,residualDegree2,residualDegree3,residualDegree4,residualDegree5,residualDegree6,residualDegree7,residualDegree8]
def residualPieces (i : Fin 3) (d : Fin 9) : Coefficients := residualPolynomials d i
def residualRanges : Fin 9 → DiskTimePolynomial.Certificate 3 := ![residualRange0,residualRange1,residualRange2,residualRange3,residualRange4,residualRange5,residualRange6,residualRange7,residualRange8]
def residualBases : Fin 3 → Fin 9 → Coefficients := ![basePieces0,basePieces1,basePieces2]
def residualFactors : Fin 3 → Partition := ![coupledPartition0,coupledPartition1,coupledPartition2]

theorem residualFactors_checked : ∀ i, (residualFactors i).Valid (mkRat (1) 10) := by
  intro i
  fin_cases i
  · exact coupledPartition0_checked
  · exact coupledPartition1_checked
  · exact coupledPartition2_checked

theorem residualPieces_checked : ∀ i d, zero (subtract
    (add (residualBases i d) (scale modelInput.K
      (degreeProduct d.val cubeDeviation (residualFactors i)))) (residualPieces i d)) := by
  intro i d
  fin_cases i <;> fin_cases d
  · exact residualPart0_0_checked
  · exact residualPart0_1_checked
  · exact residualPart0_2_checked
  · exact residualPart0_3_checked
  · exact residualPart0_4_checked
  · exact residualPart0_5_checked
  · exact residualPart0_6_checked
  · exact residualPart0_7_checked
  · exact residualPart0_8_checked
  · exact residualPart1_0_checked
  · exact residualPart1_1_checked
  · exact residualPart1_2_checked
  · exact residualPart1_3_checked
  · exact residualPart1_4_checked
  · exact residualPart1_5_checked
  · exact residualPart1_6_checked
  · exact residualPart1_7_checked
  · exact residualPart1_8_checked
  · exact residualPart2_0_checked
  · exact residualPart2_1_checked
  · exact residualPart2_2_checked
  · exact residualPart2_3_checked
  · exact residualPart2_4_checked
  · exact residualPart2_5_checked
  · exact residualPart2_6_checked
  · exact residualPart2_7_checked
  · exact residualPart2_8_checked

theorem residualRanges_checked : ∀ d,
    BallNormProfile.CertificateValid (residualRanges d) (fun i => residualPieces i d) (mkRat (1) 10) := by
  intro d
  fin_cases d
  · exact residualRange0_checked
  · exact residualRange1_checked
  · exact residualRange2_checked
  · exact residualRange3_checked
  · exact residualRange4_checked
  · exact residualRange5_checked
  · exact residualRange6_checked
  · exact residualRange7_checked
  · exact residualRange8_checked

def residualCoreBound : List ℚ :=
  PolynomialBounds.add (profileSum fun d => (residualRanges d).bound 1)
    (PolynomialBounds.scale modelInput.K
      (profileSum fun i => discardedProfile 8 cubeDeviation (residualFactors i)))

theorem residualCore_bound {x : Fin 3 → ℝ} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤((1/10:ℚ):ℝ)^2) (ht : 0≤t) :
    enorm (value3 (modelInput.residualWith offsetCube) x t)≤
      PolynomialOrder.value residualCoreBound t := by
  have hs : mkRat 1 10=(1/10:ℚ) := by decide +kernel
  have hx' : x 0^2+x 1^2+x 2^2≤((mkRat 1 10:ℚ):ℝ)^2 := by
    simpa only [hs] using hx
  apply modelInput.residual_enclosure offsetCube 8 cubeDeviation residualFactors
    residualBases residualPieces residualRanges model_K_nonnegative cubeDeviation_checked
    residualFactors_checked residualPieces_checked residualRanges_checked hx' ht
  · intro i
    fin_cases i
    · exact basePieces0_value x t
    · exact basePieces1_value x t
    · exact basePieces2_value x t

  · exact cubeDeviation_value x t
  · intro i
    fin_cases i
    · exact coupledPartition0_value x t
    · exact coupledPartition1_value x t
    · exact coupledPartition2_value x t

def residualBound : List ℚ := PolynomialBounds.add residualCoreBound
  (PolynomialBounds.scale modelInput.K
    (PolynomialBounds.multiply offsetCubeTail (coupledRange.bound 1)))

/-- Includes the entire cubic inverse-radius factor, not only its retained
polynomial. No trajectory samples are premises of this theorem. -/
theorem residual_bound {x : Fin 3 → ℝ} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤((1/10:ℚ):ℝ)^2) (ht : 0≤t) :
    enorm (value3 modelInput.residual x t)≤PolynomialOrder.value residualBound t := by
  have hK : 0≤(modelInput.K:ℝ) := by exact_mod_cast model_K_nonnegative
  have h := modelInput.full_residual_enclosure offsetCube x t hK
    (residualCore_bound hx ht) (offsetCube_bound hx ht) (coupled_bound hx ht)
  simpa only [residualBound,PolynomialOrder.value_add,PolynomialOrder.value_scale,
    DiskPolynomial.value_multiply,mul_assoc] using h

end GNC.OrbitalComparison.JointErrorData
