import GNC.Applications.OrbitalComparison.TDSTTData.Cartesian2.Prediction
import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Prediction

/-! Matched physical guarantees for the two fitted directional queries.
The ODE, initial state, pointing ball and horizon are identical. Ordering
the certified budgets does not by itself order the actual predictor errors. -/
noncomputable section
namespace GNC.OrbitalComparison.TDSTTComparison
open Set TDSTTData

def toCartesian {φ : Vec3} (X : Lie2.Motion φ) : Cartesian2.Motion φ where
  p := X.p
  v := X.v
  continuous_p := X.continuous_p
  continuous_v := X.continuous_v
  initial_p := X.initial_p.trans ((Lie2.position_initial φ).trans (Cartesian2.position_initial φ).symm)
  initial_v := X.initial_v.trans ((Lie2.velocity_initial φ).trans (Cartesian2.velocity_initial φ).symm)
  derivative_p := X.derivative_p
  derivative_v := X.derivative_v

def toLie {φ : Vec3} (X : Cartesian2.Motion φ) : Lie2.Motion φ where
  p := X.p
  v := X.v
  continuous_p := X.continuous_p
  continuous_v := X.continuous_v
  initial_p := X.initial_p.trans ((Cartesian2.position_initial φ).trans (Lie2.position_initial φ).symm)
  initial_v := X.initial_v.trans ((Cartesian2.velocity_initial φ).trans (Lie2.velocity_initial φ).symm)
  derivative_p := X.derivative_p
  derivative_v := X.derivative_v

theorem matched_physical_certificates {φ : Vec3}
    (hφ : φ 0^2+φ 1^2+φ 2^2≤((1/10:ℚ):ℝ)^2) :
    (∃ _X : Lie2.Motion φ, True) ∧
    (∀ X : Lie2.Motion φ, ∀ t ∈ Icc (0:ℝ) 1,
      (7000000*‖X.p t-Lie2.candidatePosition φ t‖≤(Lie2.positionUpper:ℝ) ∧
        (7000000/120)*‖X.v t-Lie2.deliveredVelocity φ t‖≤(Lie2.velocityUpper:ℝ)) ∧
      (7000000*‖X.p t-Cartesian2.candidatePosition φ t‖≤(Cartesian2.positionUpper:ℝ) ∧
        (7000000/120)*‖X.v t-Cartesian2.deliveredVelocity φ t‖≤(Cartesian2.velocityUpper:ℝ))) := by
  obtain ⟨X,_⟩ := Lie2.exists_motion hφ
  refine ⟨⟨X,trivial⟩,?_⟩
  intro Y t ht
  exact ⟨(Lie2.physical_prediction hφ).2 Y t ht,
    (Cartesian2.physical_prediction hφ).2 (toCartesian Y) t ht⟩

/-- These are ratios of the proved budgets for these specific candidates,
not an error ratio for arbitrary Cartesian algorithms. -/
theorem certified_budgets_compare :
    1600*Lie2.positionUpper<Cartesian2.positionUpper ∧
    1580*Lie2.velocityUpper<Cartesian2.velocityUpper := by
  decide +kernel

end GNC.OrbitalComparison.TDSTTComparison
