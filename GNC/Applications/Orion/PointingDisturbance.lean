import GNC.Applications.Orion.Propulsion
import GNC.Control.ControllerThrust

/-! A synthetic attitude-controller contract at the public Orion engine scale.

Time is in seconds. The selected gains are kq=kz=1/s and κ=1/s². The
inertia-normalized torque/model residual is at most 0.01 rad/s² in Euclidean
norm, and the initial storage is at most 0.00005/s². These are explicit
illustrative design requirements, not Orion flight-controller parameters or
measured motor tolerances. The controller ODE is assumed realized; actuator
authority, chart continuation and orbital arrival are separate obligations.

The conclusions quantify arbitrary admissible time histories on all three
attitude axes, including constant bias. The acceleration follows the proved
mass-depleting force model. They concern thrust impulse, not final orbital
velocity (which also includes gravity) or propellant savings.
-/
noncomputable section
open Matrix Real Set MeasureTheory
open scoped Matrix.Norms.Operator
namespace GNC.Orion.PointingDisturbance
open LogBackstepping ThrustSupport Propulsion

def disturbanceLimit : ℝ := 1/100
def storageLimit : ℝ := disturbanceLimit^2/2

structure AttitudeContract (q z d : ℝ → Vec3) : Prop where
  attitude : ∀ t ∈ Icc 0 duration,
    HasDerivAt q ((-1 : ℝ) • q t+Jacobian.inverseAt (-q t) (z t)) t
  rate : ∀ t ∈ Icc 0 duration,
    HasDerivAt z ((-1 : ℝ) • z t-(1 : ℝ) • q t+d t) t
  disturbance : ∀ t ∈ Icc 0 duration, enorm (d t) ≤ disturbanceLimit
  initial : rateStorage 1 (q 0) (z 0) ≤ storageLimit

theorem AttitudeContract.storage_bound {q z d : ℝ → Vec3} (hc : AttitudeContract q z d) :
    ∀ t ∈ Icc 0 duration, rateStorage 1 (q t) (z t) ≤ storageLimit := by
  apply disturbed_rate_uniform_bound (kq := 1) (kz := 1) (c := 1) (ell := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hc.attitude hc.rate hc.disturbance hc.initial
  norm_num [storageLimit]

theorem AttitudeContract.pointing_cap {q z d : ℝ → Vec3} (hc : AttitudeContract q z d)
    {t : ℝ} (ht : t ∈ Icc 0 duration) (n : Vec3) (hn : n ⬝ᵥ n = 1) :
    rotate (rotationExp (q t)) n ∈ Cap n (1-storageLimit) := by
  simpa only [div_one] using
    rateStorage_cap (q t) (z t) n (by norm_num : (0 : ℝ) < 1) hn (hc.storage_bound t ht)

def thrustError (q n : Vec3) (t : ℝ) : Vec3 :=
  acceleration t • (rotate (rotationExp q) n-n)

theorem AttitudeContract.axial_error {q z d : ℝ → Vec3} (hc : AttitudeContract q z d)
    {t : ℝ} (ht : t ∈ Icc 0 duration) (n : Vec3) (hn : n ⬝ᵥ n = 1) :
    -(acceleration t*storageLimit) ≤ n ⬝ᵥ thrustError (q t) n t ∧
      n ⬝ᵥ thrustError (q t) n t ≤ 0 := by
  simpa only [div_one, neg_mul, thrustError] using rateStorage_axial (q t) (z t) n
    (by norm_num : (0 : ℝ) < 1) hn (hc.storage_bound t ht) (acceleration_nonneg ht)

theorem AttitudeContract.vector_error {q z d : ℝ → Vec3} (hc : AttitudeContract q z d)
    {t : ℝ} (ht : t ∈ Icc 0 duration) (n : Vec3) (hn : n ⬝ᵥ n = 1) :
    enorm (thrustError (q t) n t) ≤ acceleration t*disturbanceLimit := by
  have h := cap_in_chord_ball n _ (1-storageLimit) disturbanceLimit hn
    (hc.pointing_cap ht n hn) (by norm_num [disturbanceLimit])
    (by norm_num [storageLimit, disturbanceLimit])
  rw [thrustError, enorm_smul, abs_of_nonneg (acceleration_nonneg ht)]
  exact mul_le_mul_of_nonneg_left h (acceleration_nonneg ht)

theorem AttitudeContract.thrustError_continuousOn {q z d : ℝ → Vec3}
    (hc : AttitudeContract q z d) {n : ℝ → Vec3} (hn : ContinuousOn n (Icc 0 duration)) :
    ContinuousOn (fun t => thrustError (q t) (n t) t) (Icc 0 duration) := by
  have hq : ContinuousOn q (Icc 0 duration) :=
    fun t ht => (hc.attitude t ht).continuousAt.continuousWithinAt
  have hs := Cayley.contDiff_skew.continuous.comp_continuousOn hq
  have he := NormedSpace.exp_continuous.comp_continuousOn hs
  have hm : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × Vec3 => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact acceleration_continuousOn.smul ((hm.comp_continuousOn (he.prodMk hn)).sub hn)

/-- Known mass variation is integrated exactly. For a changing reference
direction this measures accumulated instantaneous axial loss. For a fixed
inertial direction it is the axial component of the net thrust-impulse error. -/
theorem AttitudeContract.axial_impulse {q z d : ℝ → Vec3} (hc : AttitudeContract q z d)
    {n : ℝ → Vec3} (hnc : ContinuousOn n (Icc 0 duration))
    (hn : ∀ t ∈ Icc 0 duration, n t ⬝ᵥ n t = 1) :
    0 ≤ (∫ t in (0 : ℝ)..duration, -(n t ⬝ᵥ thrustError (q t) (n t) t)) ∧
      (∫ t in (0 : ℝ)..duration, -(n t ⬝ᵥ thrustError (q t) (n t) t)) ≤ 4433/400000 := by
  have hT : (0 : ℝ) ≤ duration := by norm_num [duration]
  have hp : Continuous (fun p : Vec3 × Vec3 => p.1 ⬝ᵥ p.2) :=
    continuous_fst.dotProduct continuous_snd
  have hi := (hp.comp_continuousOn
    (hnc.prodMk (hc.thrustError_continuousOn hnc))).neg.intervalIntegrable_of_Icc (μ := volume) hT
  change IntervalIntegrable (fun t => -(n t ⬝ᵥ thrustError (q t) (n t) t)) volume 0 duration at hi
  have hb : (∫ t in (0 : ℝ)..duration, acceleration t*storageLimit) =
      scalarImpulse*storageLimit := by
    rw [intervalIntegral.integral_mul_const, integral_acceleration]
  constructor
  · apply intervalIntegral.integral_nonneg hT
    intro t ht
    exact neg_nonneg.mpr (hc.axial_error ht (n t) (hn t ht)).2
  · have h := intervalIntegral.integral_mono_on hT hi
      (acceleration_integrable.mul_const storageLimit) (fun t ht =>
        by linarith [(hc.axial_error ht (n t) (hn t ht)).1])
    rw [hb] at h
    have hs := scalar_impulse_bounds.2
    norm_num [storageLimit, disturbanceLimit] at *
    linarith

/-- A Euclidean enclosure of the net three-dimensional thrust-impulse error.
No cancellation, constant disturbance, or fixed rotation axis is assumed. -/
theorem AttitudeContract.vector_impulse {q z d : ℝ → Vec3} (hc : AttitudeContract q z d)
    {n : ℝ → Vec3} (hnc : ContinuousOn n (Icc 0 duration))
    (hn : ∀ t ∈ Icc 0 duration, n t ⬝ᵥ n t = 1) :
    enorm (∫ t in (0 : ℝ)..duration, thrustError (q t) (n t) t) ≤ 4433/2000 := by
  have hT : (0 : ℝ) ≤ duration := by norm_num [duration]
  have hcontinuous := hc.thrustError_continuousOn hnc
  have h := enorm_integral_le _ hT (hcontinuous.intervalIntegrable_of_Icc hT)
  have he := intervalIntegral.integral_mono_on hT
    ((euclideanEquiv.continuous.comp_continuousOn hcontinuous).norm.intervalIntegrable_of_Icc hT)
    (acceleration_integrable.mul_const disturbanceLimit)
    (fun t ht => hc.vector_error ht (n t) (hn t ht))
  rw [intervalIntegral.integral_mul_const, integral_acceleration] at he
  change (∫ t in (0 : ℝ)..duration, enorm (thrustError (q t) (n t) t)) ≤
    scalarImpulse*disturbanceLimit at he
  have hs := scalar_impulse_bounds.2
  norm_num [disturbanceLimit] at *
  linarith

/-- With a moving reference attitude, rotate the thrust error before
integrating. Euclidean invariance gives the same bound even though rotations
cannot in general be pulled outside the impulse integral. -/
theorem AttitudeContract.rotated_vector_impulse {q z d : ℝ → Vec3}
    (hc : AttitudeContract q z d) (R : ℝ → SO3)
    (hR : ContinuousOn (fun t => (R t).val) (Icc 0 duration))
    {n : ℝ → Vec3} (hnc : ContinuousOn n (Icc 0 duration))
    (hn : ∀ t ∈ Icc 0 duration, n t ⬝ᵥ n t = 1) :
    enorm (∫ t in (0 : ℝ)..duration, rotate (R t) (thrustError (q t) (n t) t)) ≤
      4433/2000 := by
  have hT : (0 : ℝ) ≤ duration := by norm_num [duration]
  have hm : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × Vec3 => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hr := hm.comp_continuousOn (hR.prodMk (hc.thrustError_continuousOn hnc))
  have h := enorm_integral_le _ hT (hr.intervalIntegrable_of_Icc (μ := volume) hT)
  change enorm (∫ t in (0 : ℝ)..duration, rotate (R t) (thrustError (q t) (n t) t)) ≤
    ∫ t in (0 : ℝ)..duration, enorm (rotate (R t) (thrustError (q t) (n t) t)) at h
  simp_rw [rotate_enorm] at h
  have he := intervalIntegral.integral_mono_on hT
    ((euclideanEquiv.continuous.comp_continuousOn
      (hc.thrustError_continuousOn hnc)).norm.intervalIntegrable_of_Icc hT)
    (acceleration_integrable.mul_const disturbanceLimit)
    (fun t ht => hc.vector_error ht (n t) (hn t ht))
  change (∫ t in (0 : ℝ)..duration, enorm (thrustError (q t) (n t) t)) ≤
    ∫ t in (0 : ℝ)..duration, acceleration t*disturbanceLimit at he
  rw [intervalIntegral.integral_mul_const, integral_acceleration] at he
  have hs := scalar_impulse_bounds.2
  norm_num [disturbanceLimit] at *
  linarith

/-- The accumulated instantaneous-axis loss is independent of which
reference frame represents each sample. This is not final orbital velocity. -/
theorem AttitudeContract.rotated_axial_impulse {q z d : ℝ → Vec3}
    (hc : AttitudeContract q z d) (R : ℝ → SO3)
    {n : ℝ → Vec3} (hnc : ContinuousOn n (Icc 0 duration))
    (hn : ∀ t ∈ Icc 0 duration, n t ⬝ᵥ n t = 1) :
    0 ≤ (∫ t in (0 : ℝ)..duration,
      -(rotate (R t) (n t) ⬝ᵥ rotate (R t) (thrustError (q t) (n t) t))) ∧
    (∫ t in (0 : ℝ)..duration,
      -(rotate (R t) (n t) ⬝ᵥ rotate (R t) (thrustError (q t) (n t) t))) ≤ 4433/400000 := by
  simp_rw [rotate_dot]
  exact hc.axial_impulse hnc hn

/-- The hypotheses allow nonzero steady disturbance. This exact equilibrium
also prevents interpreting the storage certificate as automatic bias rejection. -/
theorem constant_bias_contract (b : Vec3) (hb : enorm b ≤ disturbanceLimit) :
    AttitudeContract (fun _ => (1/2 : ℝ) • b) (fun _ => (1/2 : ℝ) • b) (fun _ => b) := by
  have he := constant_disturbance_equilibrium ((1/2 : ℝ) • b) (1 : ℝ) 1 1
  simp only [one_smul, one_mul] at he
  constructor
  · intro t _
    convert hasDerivAt_const t ((1/2 : ℝ) • b) using 1
    exact he.1
  · intro t _
    convert hasDerivAt_const t ((1/2 : ℝ) • b) using 1
    module
  · exact fun _ _ => hb
  · have hs : enorm b ^ 2 ≤ disturbanceLimit^2 := by
      nlinarith [enorm_nonneg b]
    unfold rateStorage storageLimit
    rw [← enorm_sq, enorm_smul]
    norm_num
    nlinarith [sq_nonneg disturbanceLimit]

end GNC.Orion.PointingDisturbance
