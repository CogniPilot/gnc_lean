import GNC.Applications.OrbitalComparison.PoweredCircularComparators
import GNC.Applications.OrbitalComparison.FiniteResponseData
import GNC.Dynamics.CandidateOrbitExistence
import GNC.Dynamics.ForcedOrbitUniqueness
import GNC.Lie.RotationIsometry

/-! Existence and uniqueness for the powered-circle certificate.

The physical orbit is constructed for every three-dimensional pointing
vector in the stated ball. No unknown-orbit radius is a premise. The coarse
existence region is derived from the dimensionless gravity gain; it is not
an allowance added to the sharp prediction certificate.
-/
noncomputable section
namespace GNC.OrbitalComparison.PoweredCircularExistence
open Set
open PoweredCircularLogTube
open GeometricSTMPrediction (E force)

/-- For k = 2 mu < 1, this radius has cube at least k:
(k+2)^3 - 27k = (k-1)^2 (k+8). -/
def innerRadius : ℚ := (2+2*FiniteResponseData.mu)/3

/-- Divide the available annulus between the existence and uniqueness
arguments. These are construction margins, not predictor error budgets. -/
def extensionRadius : ℚ := (1-innerRadius)/4
def orbitRadius : ℝ := (1+(innerRadius:ℝ))/2

theorem region_checks :
    0<(innerRadius:ℝ) ∧ 0<extensionRadius ∧
    0<orbitRadius ∧
    (innerRadius:ℝ)<orbitRadius ∧
    orbitRadius+2*(extensionRadius:ℝ)=1 ∧
    2*μ/(innerRadius:ℝ)^3≤1 ∧ 2*μ/orbitRadius^3≤1 ∧
    4*(angleRadius*U)≤(extensionRadius:ℝ) := by
  norm_num [innerRadius, extensionRadius, orbitRadius, FiniteResponseData.mu,
    μ, U, earthMu, duration, lengthScale, physicalAcceleration, angleRadius]

theorem reference_continuous : Continuous reference :=
  continuous_iff_continuousAt.mpr fun t => (reference_derivative t).continuousAt

theorem referenceVelocity_continuous : Continuous referenceVelocity :=
  continuous_iff_continuousAt.mpr fun t => (reference_velocity_derivative t).continuousAt

theorem thrust_continuous : Continuous thrust := reference_continuous.const_smul U

theorem rotated_thrust_continuous (φ : Vec3) :
    Continuous (fun t => force φ (thrust t)) :=
  (rotationIsometry (rotationExp φ)).continuous.comp thrust_continuous

theorem referenceAcceleration_continuous :
    Continuous (fun t => Gravity.field μ (reference t)+thrust t) := by
  simp_rw [Gravity.field, reference_norm]
  exact (reference_continuous.const_smul _).add thrust_continuous

/-- A motion solves the full inverse-square ODE, not its linearization.
Normalized time is physical time / 600 s; position is in units of 7000 km. -/
structure Motion (φ : Vec3) where
  p : ℝ → E
  v : ℝ → E
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=reference 0
  initial_v : v 0=referenceVelocity 0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (Gravity.field μ (p t)+force φ (thrust t)) t

/-- Construct an orbit on the whole burn, and prove its noncollision.
The only uncertainty assumption is the declared initial attitude ball. -/
theorem exists_motion (φ : Vec3) (hφ : enorm φ≤angleRadius) :
    ∃ X : Motion φ, ∀ t ∈ Icc (0:ℝ) 1, orbitRadius≤‖X.p t‖ := by
  obtain ⟨p,v,hp,hv,hp0,hv0,hdp,hdv,hr⟩ := Gravity.exists_near_candidate
    (μ := μ) (scale := 1) (r := orbitRadius) (R := extensionRadius)
    μ_nonneg (by norm_num) region_checks.2.2.1 region_checks.2.1.le
    (by simpa using region_checks.2.2.2.2.2.2.1)
    reference referenceVelocity (fun t => Gravity.field μ (reference t)+thrust t)
    (fun t => force φ (thrust t))
    reference_continuous referenceVelocity_continuous referenceAcceleration_continuous
    (rotated_thrust_continuous φ)
    (fun t _ => reference_derivative t) (fun t _ => reference_velocity_derivative t)
    (by intro t _; rw [reference_norm, region_checks.2.2.2.2.1])
    (D := angleRadius*U) (mul_nonneg (by norm_num [angleRadius]) U_nonneg)
    (by
      intro t _
      simpa only [one_smul, add_sub_add_left_eq_sub] using
        (PoweredCircularComparators.input_sizes φ hφ t).2)
    region_checks.2.2.2.2.2.2.2
  exact ⟨⟨p,v,hp,hv,hp0,hv0,hdp,by simpa only [one_smul] using hdv⟩,hr⟩

/-- Chosen from the proved existence result, not supplied as an oracle. -/
def trajectory (φ : Vec3) (hφ : enorm φ≤angleRadius) : Motion φ :=
  Classical.choose (exists_motion φ hφ)

theorem trajectory_radius (φ : Vec3) (hφ : enorm φ≤angleRadius)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    orbitRadius≤‖(trajectory φ hφ).p t‖ :=
  Classical.choose_spec (exists_motion φ hφ) t ht

/-- Any other classical solution of the same IVP agrees on the burn.
It need not supply its own proximity or noncollision hypothesis. -/
theorem unique (φ : Vec3) (hφ : enorm φ≤angleRadius) (X : Motion φ) :
    ∀ t ∈ Icc (0:ℝ) 1,
      X.p t=(trajectory φ hφ).p t ∧ X.v t=(trajectory φ hφ).v t := by
  let Y := trajectory φ hφ
  apply ForcedOrbitUniqueness.unique μ 1 μ_nonneg (by norm_num)
    X.p X.v Y.p Y.v (fun t => force φ (thrust t))
    X.continuous_p X.continuous_v Y.continuous_p Y.continuous_v
    X.derivative_p (by simpa only [one_smul] using X.derivative_v)
    Y.derivative_p (by simpa only [one_smul] using Y.derivative_v)
    (X.initial_p.trans Y.initial_p.symm) (X.initial_v.trans Y.initial_v.symm)
    (r := (innerRadius:ℝ)) (M := orbitRadius-(innerRadius:ℝ))
    region_checks.1 (sub_pos.mpr region_checks.2.2.2.1)
    (by simpa using region_checks.2.2.2.2.2.1)
  intro t ht
  simpa only [add_sub_cancel] using trajectory_radius φ hφ ht

end GNC.OrbitalComparison.PoweredCircularExistence
