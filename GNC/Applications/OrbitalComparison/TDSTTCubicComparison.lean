import GNC.Applications.OrbitalComparison.TDSTTData.Lie2.Prediction
import GNC.Applications.OrbitalComparison.TDSTTData.FullCartesian3.Prediction

/-! The refined full Cartesian cubic and Lie rank-two certificates concern
the same physical motions. The smaller Cartesian budget is not an ordering
of the actual errors, nor a proof of construction or runtime complexity. -/
noncomputable section
namespace GNC.OrbitalComparison.TDSTTCubicComparison
open Set TDSTTData

def toCubic {φ : Vec3} (X : Lie2.Motion φ) : FullCartesian3.Motion φ where
  p := X.p
  v := X.v
  continuous_p := X.continuous_p
  continuous_v := X.continuous_v
  initial_p := X.initial_p.trans ((Lie2.position_initial φ).trans
    (FullCartesian3.position_initial φ).symm)
  initial_v := X.initial_v.trans ((Lie2.velocity_initial φ).trans
    (FullCartesian3.velocity_initial φ).symm)
  derivative_p := X.derivative_p
  derivative_v := X.derivative_v

theorem matched_physical_certificates {φ : Vec3}
    (hφ : φ 0^2+φ 1^2+φ 2^2≤((1/10:ℚ):ℝ)^2) :
    (∃ _X : Lie2.Motion φ, True) ∧
    (∀ X : Lie2.Motion φ, ∀ t ∈ Icc (0:ℝ) 1,
      (7000000*‖X.p t-Lie2.candidatePosition φ t‖≤(Lie2.positionUpper:ℝ) ∧
        (7000000/120)*‖X.v t-Lie2.deliveredVelocity φ t‖≤(Lie2.velocityUpper:ℝ)) ∧
      (7000000*‖X.p t-FullCartesian3.candidatePosition φ t‖≤(FullCartesian3.positionUpper:ℝ) ∧
        (7000000/120)*‖X.v t-FullCartesian3.deliveredVelocity φ t‖≤(FullCartesian3.velocityUpper:ℝ))) := by
  obtain ⟨X,_⟩ := Lie2.exists_motion hφ
  refine ⟨⟨X,trivial⟩,?_⟩
  intro Y t ht
  exact ⟨(Lie2.physical_prediction hφ).2 Y t ht,
    (FullCartesian3.physical_prediction hφ).2 (toCubic Y) t ht⟩

theorem certified_targets :
    FullCartesian3.positionUpper < 1/1000 ∧ Lie2.positionUpper < 1/1000 ∧
    FullCartesian3.velocityUpper < 1/10000 ∧ Lie2.velocityUpper < 1/10000 := by
  decide +kernel

/-- A comparison of certified upper bounds, not actual errors. -/
theorem cubic_budgets_smaller :
    FullCartesian3.positionUpper < Lie2.positionUpper ∧
    FullCartesian3.velocityUpper < Lie2.velocityUpper := by decide +kernel

end GNC.OrbitalComparison.TDSTTCubicComparison
