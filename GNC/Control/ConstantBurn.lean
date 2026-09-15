import GNC.Control.ThrustIntegral
import GNC.Control.Propellant
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Constant inertial acceleration can match a prescribed propulsive
velocity increment with minimum accumulated acceleration. This is a statement
about the thrust integral. It does not assert preservation of terminal
position, gravity response, path constraints or a pointing uncertainty set.
The centered first moment below exposes the missing position condition.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.ConstantBurn
open Matrix MeasureTheory Set

def acceleration (d : Vec3) (T : ℝ) : Vec3 := (1/T) • d

theorem impulse (d : Vec3) {T : ℝ} (hT : T ≠ 0) :
    (∫ _t in (0:ℝ)..T, acceleration d T) = d := by
  simp [acceleration, intervalIntegral.integral_const, smul_smul, hT]

theorem cost (d : Vec3) {T : ℝ} (hT : 0 < T) :
    (∫ _t in (0:ℝ)..T, enorm (acceleration d T)) = enorm d := by
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    acceleration, enorm_smul, abs_of_pos (one_div_pos.mpr hT)]
  field_simp

/-- The lower bound holds for every integrable acceleration history with
the specified thrust integral, without requiring a particular parameterization. -/
theorem minimum_cost (u : ℝ → Vec3) {T : ℝ} (hT : 0 < T)
    (hu : IntervalIntegrable u volume 0 T) :
    (∫ _t in (0:ℝ)..T, enorm (acceleration (∫ t in (0:ℝ)..T, u t) T)) ≤
      ∫ t in (0:ℝ)..T, enorm (u t) := by
  rw [cost _ hT]
  exact ThrustSupport.enorm_integral_le u hT.le hu

theorem propellant_no_greater (u : ℝ → Vec3) {T mass exhaust : ℝ}
    (hT : 0 < T) (hm : 0 ≤ mass) (he : 0 < exhaust)
    (hu : IntervalIntegrable u volume 0 T) :
    Propellant.consumedMass mass exhaust (enorm (∫ t in (0:ℝ)..T, u t)) ≤
      Propellant.consumedMass mass exhaust (∫ t in (0:ℝ)..T, enorm (u t)) :=
  Propellant.consumed_mono hm he (ThrustSupport.enorm_integral_le u hT.le hu)

/-- The constant replacement does not exceed a uniform acceleration limit. -/
theorem acceleration_limit (d : Vec3) {T limit : ℝ} (hT : 0 < T)
    (hd : enorm d ≤ T*limit) : enorm (acceleration d T) ≤ limit := by
  rw [acceleration, enorm_smul, abs_of_pos (one_div_pos.mpr hT), one_div_mul_eq_div]
  rw [div_le_iff₀ hT]
  simpa only [mul_comm] using hd

def direction (d : Vec3) : Vec3 := (enorm d)⁻¹ • d

theorem direction_unit {d : Vec3} (hd : d ≠ 0) : enorm (direction d) = 1 := by
  have hn : 0 < enorm d := lt_of_le_of_ne (enorm_nonneg d)
    (Ne.symm (mt (enorm_eq_zero_iff d).mp hd))
  simp [direction, enorm_smul, abs_of_pos (inv_pos.mpr hn), hn.ne']

theorem along_direction {d : Vec3} (hd : d ≠ 0) (T : ℝ) :
    acceleration d T = (enorm d/T) • direction d := by
  have hn : enorm d ≠ 0 := mt (enorm_eq_zero_iff d).mp hd
  simp only [acceleration, direction, smul_smul]
  congr 1
  field_simp

/-- Thrust's terminal position contribution for a double integrator. -/
def positionMoment (u : ℝ → Vec3) (T : ℝ) : Vec3 :=
  ∫ t in (0:ℝ)..T, (T-t) • u t

def centeredMoment (u : ℝ → Vec3) (T : ℝ) : Vec3 :=
  ∫ t in (0:ℝ)..T, (t-T/2) • u t

/-- Connect the moments to actual position/velocity derivatives. No gravity
or other acceleration is omitted: `u` is the complete acceleration here. -/
theorem double_integrator_endpoint (p v u : ℝ → Vec3) (hu : Continuous u)
    {T : ℝ} (hT : 0 ≤ T)
    (hp : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt v (u t) t) :
    v T-v 0 = (∫ t in (0:ℝ)..T, u t) ∧
      p T-p 0-T • v 0 = positionMoment u T := by
  have hd : ∀ t ∈ Icc (0:ℝ) T,
      HasDerivAt (fun s => p s+(T-s) • v s) ((T-t) • u t) t := by
    intro t ht
    convert (hp t ht).add (((hasDerivAt_const t T).sub (hasDerivAt_id t)).smul (hv t ht)) using 1
    simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hT] using ht))
    (((continuous_const.sub continuous_id).smul hu).intervalIntegrable 0 T)
  have hj := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hv t (by simpa only [uIcc_of_le hT] using ht)) (hu.intervalIntegrable 0 T)
  refine ⟨hj.symm,?_⟩
  simp only [sub_self, zero_smul, add_zero, sub_zero] at hi
  change p T-p 0-T • v 0 = ∫ t in (0:ℝ)..T, (T-t) • u t
  rw [hi]
  abel

theorem position_decomposition (u : ℝ → Vec3) (hu : Continuous u) (T : ℝ) :
    positionMoment u T = (T/2) • (∫ t in (0:ℝ)..T, u t)-centeredMoment u T := by
  have hf : (fun t => (T-t) • u t) =
      (fun t => (T/2) • u t-(t-T/2) • u t) := by
    funext t
    rw [← sub_smul]
    congr 1
    ring
  have h1 : IntervalIntegrable (fun t : ℝ => (T/2) • u t) volume 0 T :=
    (continuous_const.smul hu).intervalIntegrable 0 T
  have h2 : IntervalIntegrable (fun t : ℝ => (t-T/2) • u t) volume 0 T :=
    ((continuous_id.sub continuous_const).smul hu).intervalIntegrable 0 T
  rw [positionMoment, hf, intervalIntegral.integral_sub h1 h2]
  simp only [intervalIntegral.integral_smul, centeredMoment]

theorem centered_constant (v : Vec3) (T : ℝ) : centeredMoment (fun _ => v) T = 0 := by
  have h : (∫ t in (0:ℝ)..T, t-T/2) = 0 := by
    have ht : IntervalIntegrable (fun t : ℝ => t) volume 0 T := continuous_id.intervalIntegrable 0 T
    have hc : IntervalIntegrable (fun _ : ℝ => T/2) volume 0 T := continuous_const.intervalIntegrable 0 T
    rw [intervalIntegral.integral_sub ht hc,
      integral_id, intervalIntegral.integral_const]
    simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), smul_eq_mul]
    ring
  rw [centeredMoment, intervalIntegral.integral_smul_const, h, zero_smul]

/-- Equal net delta-v also preserves the double-integrator position moment
exactly when the original acceleration has zero centered first moment. -/
theorem position_preserved_iff (u : ℝ → Vec3) (hu : Continuous u) {T : ℝ} (hT : 0 < T) :
    positionMoment (fun _ => acceleration (∫ t in (0:ℝ)..T, u t) T) T = positionMoment u T ↔
      centeredMoment u T = 0 := by
  rw [position_decomposition _ continuous_const, impulse _ hT.ne', centered_constant, sub_zero,
    position_decomposition u hu]
  constructor
  · intro h
    have hh := (eq_sub_iff_add_eq).mp h
    have he := add_left_cancel (show (T/2) • (∫ t in (0:ℝ)..T, u t)+centeredMoment u T =
      (T/2) • (∫ t in (0:ℝ)..T, u t)+0 by simpa using hh)
    exact he
  · intro h
    rw [h, sub_zero]

end GNC.ConstantBurn
