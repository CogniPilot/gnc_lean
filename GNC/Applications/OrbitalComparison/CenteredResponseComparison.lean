import GNC.Applications.OrbitalComparison.CenteredResponsePrediction
import GNC.Applications.OrbitalComparison.JointErrorPrediction

/-! Both completed certificates bound the same physical motions. This
bridge checks the ODE and initial-state identification explicitly; comparing
two unrelated existence witnesses would not establish a matched benchmark.
The theorem compares certified bounds, not the predictors' actual errors. -/
noncomputable section
namespace GNC.OrbitalComparison.CenteredResponseData
open Set

theorem same_initial_position (φ : Vec3) : position φ 0=JointErrorData.position φ 0 := by
  rw [position_initial]
  exact (congrArg (WithLp.toLp 2) (JointErrorData.initial_position_midpoint φ)).symm

theorem same_initial_velocity (φ : Vec3) : velocity φ 0=JointErrorData.velocity φ 0 := by
  rw [velocity_initial]
  exact (congrArg (WithLp.toLp 2) (JointErrorData.initial_velocity_midpoint φ)).symm

def ofJointMotion {φ : Vec3} (X : JointErrorData.Motion φ) : Motion φ where
  p := X.p
  v := X.v
  continuous_p := X.continuous_p
  continuous_v := X.continuous_v
  initial_p := X.initial_p.trans (same_initial_position φ).symm
  initial_v := X.initial_v.trans (same_initial_velocity φ).symm
  derivative_p := X.derivative_p
  derivative_v := X.derivative_v

def toJointMotion {φ : Vec3} (X : Motion φ) : JointErrorData.Motion φ where
  p := X.p
  v := X.v
  continuous_p := X.continuous_p
  continuous_v := X.continuous_v
  initial_p := X.initial_p.trans (same_initial_position φ)
  initial_v := X.initial_v.trans (same_initial_velocity φ)
  derivative_p := X.derivative_p
  derivative_v := X.derivative_v

theorem joint_attitude_domain (φ : Vec3) (hφ : enorm φ≤1/10) :
    φ 0^2+φ 1^2+φ 2^2≤(JointErrorData.sigma:ℝ)^2 := by
  have h := pow_le_pow_left₀ (enorm_nonneg φ) hφ 2
  rw [enorm_sq] at h
  simpa only [lengthSq,JointErrorData.sigma,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h

theorem centered_certificate_on_joint_motion (φ : Vec3) (hφ : enorm φ≤1/10)
    (X : JointErrorData.Motion φ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    7000000*‖X.p t-position φ t‖≤(positionUpper:ℝ) ∧
      (7000000/120)*‖X.v t-velocity φ t‖≤(velocityUpper:ℝ) :=
  (physical_prediction φ hφ).2 (ofJointMotion X) t ht

/-- Existence and both SI-unit bounds for every same physical motion. -/
theorem matched_physical_certificates (φ : Vec3) (hφ : enorm φ≤1/10) :
    (∃ _X : JointErrorData.Motion φ, True) ∧
    (∀ X : JointErrorData.Motion φ, ∀ t ∈ Icc (0:ℝ) 1,
      (7000000*‖X.p t-JointErrorData.position φ t‖≤(JointErrorData.positionUpper:ℝ) ∧
        (7000000/120)*‖X.v t-JointErrorData.velocity φ t‖≤(JointErrorData.velocityUpper:ℝ)) ∧
      (7000000*‖X.p t-position φ t‖≤(positionUpper:ℝ) ∧
        (7000000/120)*‖X.v t-velocity φ t‖≤(velocityUpper:ℝ))) := by
  obtain ⟨X,_⟩ := exists_motion φ hφ
  refine ⟨⟨toJointMotion X,trivial⟩,?_⟩
  intro Y t ht
  exact ⟨(JointErrorData.physical_prediction (joint_attitude_domain φ hφ)).2 Y t ht,
    centered_certificate_on_joint_motion φ hφ Y ht⟩

/-- The Cartesian certificate is tighter for this particular candidate and
budget construction; this does not order the actual predictor errors. -/
theorem certified_budgets_compare :
    positionUpper<JointErrorData.positionUpper ∧ velocityUpper<JointErrorData.velocityUpper := by
  decide +kernel

end GNC.OrbitalComparison.CenteredResponseData
