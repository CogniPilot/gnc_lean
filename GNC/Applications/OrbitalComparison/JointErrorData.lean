import GNC.Applications.OrbitalComparison.JointErrorData.Rho
import GNC.Applications.OrbitalComparison.JointErrorData.InverseOffset
import GNC.Applications.OrbitalComparison.JointErrorPrediction

/-! Complete physical certificate for the three-axis correlated midpoint
family: candidate ranges, scalar constraint, nonlinear residual, time envelope,
physical existence, initial-family identification and all-time SI bounds. -/
namespace GNC.OrbitalComparison.JointErrorData
open ParameterPolynomial DiskPolynomial

theorem rho_bound {x : Fin 3 → ℝ} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤((1/10:ℚ):ℝ)^2) (ht : 0≤t) :
    ‖vectorValue (rho) x t‖≤PolynomialOrder.value (rhoRange.bound 1) t :=
  BallNormProfile.certifies rhoRange (rho) rho_checked hx ht


theorem inverseOffset_bound {x : Fin 3 → ℝ} {t : ℝ}
    (hx : x 0^2+x 1^2+x 2^2≤((1/10:ℚ):ℝ)^2) (ht : 0≤t) :
    ‖vectorValue (![inverseOffset]) x t‖≤PolynomialOrder.value (inverseOffsetRange.bound 1) t :=
  BallNormProfile.certifies inverseOffsetRange (![inverseOffset]) inverseOffset_checked hx ht

end GNC.OrbitalComparison.JointErrorData
