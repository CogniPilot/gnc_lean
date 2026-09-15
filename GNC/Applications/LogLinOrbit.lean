import GNC.Dynamics.GravityGradientBound
import GNC.Analysis.STMComparison
import GNC.Analysis.ReferenceInteraction
import GNC.Analysis.FactoredSTM
import GNC.Analysis.StepComposition
import GNC.Analysis.ExponentialStep
import GNC.Analysis.InverseCertificate
import GNC.Magnus.GaussError
import GNC.Magnus.GaussSmoothRemainder
import GNC.Dynamics.RotatingVariational
import GNC.Dynamics.RadialGravityFrame
import GNC.Applications.Rendezvous.HCWCoordinates
import GNC.Applications.OrbitalComparison.QuadraticPrediction
import GNC.Applications.OrbitalComparison.NumericalPrediction
import GNC.Applications.OrbitalComparison.RegionalPrediction
import GNC.Applications.OrbitalComparison.PairedPrediction
import GNC.Applications.OrbitalComparison.CircularResidual
import GNC.Applications.OrbitalComparison.UniformData.Circle
import GNC.Applications.OrbitalComparison.UniformData.STT8
import GNC.Applications.OrbitalComparison.WeightedData.Circle10
import GNC.Applications.OrbitalComparison.WeightedData.Circle12
import GNC.Applications.OrbitalComparison.WeightedData.STT8Time10
import GNC.Applications.OrbitalComparison.WeightedData.STT8Time12
import GNC.Applications.OrbitalComparison.BernsteinData.Circle10
import GNC.Applications.OrbitalComparison.BernsteinData.Circle12
import GNC.Applications.OrbitalComparison.BernsteinData.STT8Time10
import GNC.Applications.OrbitalComparison.BernsteinData.STT8Time12
import GNC.Applications.OrbitalComparison.FullFieldData.Circle10
import GNC.Applications.OrbitalComparison.FullFieldData.Circle12
import GNC.Applications.OrbitalComparison.FullFieldData.STT8Time10
import GNC.Applications.OrbitalComparison.FullFieldData.STT8Time12
import GNC.Applications.OrbitalComparison.FullFieldData.STT10Time12
import GNC.Applications.OrbitalComparison.ExternalTaylorReview
import GNC.Applications.OrbitalComparison.ShiftedLift
import GNC.Applications.OrbitalComparison.SpatialShiftedLift
import GNC.Applications.OrbitalComparison.SpatialFlowstarReportedBounds
import GNC.Applications.OrbitalComparison.FlowstarReportedBounds
import GNC.Applications.OrbitalComparison.SpatialPointing
import GNC.Applications.OrbitalComparison.SpatialCertificates

/-! Concrete rational gravity-remainder budget used by the orbital prediction
paper. SI units. The ratio compares remainder budgets, not measured STM errors.
A trajectory tube must separately justify the radius/displacement hypotheses. -/
noncomputable section
namespace GNC.OrbitalPrediction

def earthMu : ℝ := 398600441800000

/-- Connect the physical radial-frame split to the existing checked HCW
generator. The circular condition is c=n^2 and the frame acceleration is zero. -/
theorem radial_frame_hcw (n : ℝ) :
    RotatingVariational.classicalGenerator (RadialGravityFrame.gravity (n^2))
      (RadialGravityFrame.omega n) (RadialGravityFrame.omega 0) = HCWMatrix.generator n := by
  rw [RadialGravityFrame.classical_blocks]
  simp only [HCWMatrix.generator,HCWMatrix.gravity,HCWMatrix.coriolis]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring

theorem radial_frame_log_hcw (n : ℝ) :
    RotatingVariational.logGenerator (RadialGravityFrame.gravity (n^2))
      (RadialGravityFrame.omega n) = HCWMatrix.logGenerator n := by
  unfold RotatingVariational.logGenerator HCWMatrix.logGenerator
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RadialGravityFrame.gravity,HCWMatrix.logGravity]

theorem one_km_gravity_remainder_budget :
    Gravity.remainderBound earthMu 7000000 1000 < 1/2000000 := by
  norm_num [Gravity.remainderBound, earthMu]

/-- The actual nonlinear inverse-square remainder, not a declared surrogate. -/
theorem one_km_actual_remainder (q d : Vec3) (hq : enorm q = 7000000)
    (hd : enorm d = 1000) :
    enorm (Gravity.remainder3 earthMu q d) < 1/2000000 := by
  have h := Gravity.remainder3_bound earthMu (by norm_num [earthMu]) q d
    (by rw [hq, hd]; norm_num)
  rw [hq, hd] at h
  exact h.trans_lt one_km_gravity_remainder_budget

/-- Retaining the gradient shrinks this remainder budget by more than 4000.
The right side is the gradient operator bound times displacement; this is
not a claim that every trajectory's physical prediction error shrinks so much. -/
theorem retained_gradient_budget_ratio :
    4000 * Gravity.remainderBound earthMu 7000000 1000 <
      (2*earthMu/7000000^3)*1000 := by
  norm_num [Gravity.remainderBound, earthMu]

end GNC.OrbitalPrediction
