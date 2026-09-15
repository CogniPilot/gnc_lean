import GNC.Dynamics.VariableMassThrust
import GNC.Analysis.ExponentialCertificate

/-! Orion-inspired propulsion scale, not an Artemis flight reconstruction.

Nominal OMS-E force and Isp: Belair et al., SP2024_382, Table 2.
The 207.1 s duration is that report's Table 1 RPF duration. The initial mass
is the 25,854 kg post-TLI figure in NASA's 2026 Orion factsheet, adopted here
as an illustrative initial condition, not the actual RPF ignition mass.
Rounded published parameters are exact inputs to this mathematical example.
No guidance, attitude actuator, orbital safety or fuel-saving claim is made.
-/
noncomputable section
namespace GNC.Orion.Propulsion
open Real Set MeasureTheory

def initialMass : ℝ := 25854
def thrust : ℝ := 26700
def specificImpulse : ℝ := 3151/10
def standardGravity : ℝ := 196133/20000
def exhaust : ℝ := specificImpulse*standardGravity
def duration : ℝ := 2071/10
def flow : ℝ := thrust/exhaust
def mass (t : ℝ) : ℝ := initialMass-flow*t
def acceleration (t : ℝ) : ℝ := thrust/mass t
def scalarImpulse : ℝ := exhaust*log (initialMass/mass duration)
def frozenMassImpulse : ℝ := thrust*duration/initialMass

theorem exhaust_positive : 0 < exhaust := by
  norm_num [exhaust, specificImpulse, standardGravity]

theorem mass_derivative (t : ℝ) : HasDerivAt mass (-flow) t := by
  simpa [mass] using (hasDerivAt_const t initialMass).sub ((hasDerivAt_id t).const_mul flow)

theorem mass_bounds {t : ℝ} (ht : t ∈ Icc 0 duration) :
    24064 < mass t ∧ mass t ≤ initialMass := by
  norm_num [mass, flow, thrust, exhaust, specificImpulse, standardGravity, initialMass, duration] at *
  constructor <;> linarith [ht.1, ht.2]

theorem inverse_mass_equation {t : ℝ} (ht : t ∈ Icc 0 duration) :
    HasDerivAt (fun s => (mass s)⁻¹) (flow*((mass t)⁻¹)^2) t :=
  VariableMassThrust.inverse_mass_derivative (mass_derivative t) (by linarith [(mass_bounds ht).1])

theorem accumulated_acceleration_equation {t : ℝ} (ht : t ∈ Icc 0 duration) :
    HasDerivAt (fun s => -exhaust*log (mass s)) (acceleration t) t := by
  apply VariableMassThrust.accumulated_acceleration_derivative
  · simpa [flow, neg_div] using mass_derivative t
  · linarith [(mass_bounds ht).1]
  · exact exhaust_positive.ne'

theorem acceleration_nonneg {t : ℝ} (ht : t ∈ Icc 0 duration) :
    0 ≤ acceleration t :=
  div_nonneg (by norm_num [thrust]) (by linarith [(mass_bounds ht).1])

theorem acceleration_continuousOn : ContinuousOn acceleration (Icc 0 duration) := by
  apply continuousOn_const.div
    (show ContinuousOn mass (Icc 0 duration) from
      fun t _ => (mass_derivative t).continuousAt.continuousWithinAt)
  intro t ht
  exact ne_of_gt (by linarith [(mass_bounds ht).1])

theorem acceleration_integrable : IntervalIntegrable acceleration volume 0 duration :=
  acceleration_continuousOn.intervalIntegrable_of_Icc (by norm_num [duration])

/-- The displayed logarithmic scalar impulse is the integral of the actual
variable-mass acceleration, not merely an antiderivative evaluated numerically. -/
theorem integral_acceleration : (∫ t in (0 : ℝ)..duration, acceleration t) = scalarImpulse := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => accumulated_acceleration_equation
      (by simpa only [uIcc_of_le (by norm_num [duration] : (0 : ℝ) ≤ duration)] using ht))
    acceleration_integrable
  have hm : 0 < mass duration := by
    have hb := mass_bounds (t := duration) ⟨by norm_num [duration], le_rfl⟩
    linarith [hb.1]
  rw [h, scalarImpulse, log_div (by norm_num [initialMass])
    hm.ne']
  simp only [mass, mul_zero, sub_zero]
  ring

theorem consumption_bounds :
    1789 < initialMass-mass duration ∧ initialMass-mass duration < 1790 := by
  norm_num [mass, flow, thrust, exhaust, specificImpulse, standardGravity, initialMass, duration]

theorem acceleration_bounds :
    103/100 < acceleration 0 ∧ acceleration 0 < 104/100 ∧
      110/100 < acceleration duration ∧ acceleration duration < 112/100 := by
  norm_num [acceleration, mass, flow, thrust, exhaust, specificImpulse, standardGravity,
    initialMass, duration]

theorem frozen_mass_endpoint_error :
    74/1000 < (acceleration duration-acceleration 0)/acceleration 0 ∧
      (acceleration duration-acceleration 0)/acceleration 0 < 75/1000 := by
  norm_num [acceleration, mass, flow, thrust, exhaust, specificImpulse, standardGravity,
    initialMass, duration]

/-- Bounds on the actual logarithm use released mathlib's exponential-series
inequalities. Display precision is explicit; no floating-point log is trusted. -/
theorem scalar_impulse_bounds : 22163/100 ≤ scalarImpulse ∧ scalarImpulse ≤ 4433/20 := by
  have hr : 0 < initialMass/mass duration := by
    norm_num [mass, flow, thrust, exhaust, specificImpulse, standardGravity, initialMass, duration]
  constructor
  · have hx := ExponentialCertificate.scalar_bound (r := (22163/100)/exhaust)
      (by norm_num [exhaust,specificImpulse,standardGravity])
      (by norm_num [exhaust,specificImpulse,standardGravity]) 6 (by norm_num)
    have hn : ExponentialCertificate.scalarPolynomial ((22163/100)/exhaust) 6+
        ((22163/100)/exhaust)^6*(6+1)/(Nat.factorial 6*6) ≤ initialMass/mass duration := by
      norm_num [ExponentialCertificate.scalarPolynomial, Finset.sum_range_succ,
        mass, flow, thrust, exhaust, specificImpulse, standardGravity, initialMass, duration]
    have hl := (le_log_iff_exp_le hr).mpr (hx.trans hn)
    have h := (div_le_iff₀ exhaust_positive).mp hl
    simpa [scalarImpulse, mul_comm] using h
  · have hx := sum_le_exp_of_nonneg (x := (4433/20)/exhaust)
      (by norm_num [exhaust,specificImpulse,standardGravity]) 6
    have hn : initialMass/mass duration ≤ ∑ k ∈ Finset.range 6,
        ((4433/20)/exhaust)^k/(Nat.factorial k : ℝ) := by
      norm_num [Finset.sum_range_succ, mass, flow, thrust, exhaust,
        specificImpulse, standardGravity, initialMass, duration]
    have hl := (log_le_iff_le_exp hr).mpr (hn.trans hx)
    have h := (le_div_iff₀ exhaust_positive).mp hl
    simpa [scalarImpulse, mul_comm] using h

/-- This is a scalar propulsion-model discrepancy, not orbital miss distance
or a demonstrated fuel saving. -/
theorem frozen_mass_impulse_gap :
    775/100 < scalarImpulse-frozenMassImpulse ∧ scalarImpulse-frozenMassImpulse < 778/100 := by
  have h := scalar_impulse_bounds
  norm_num [frozenMassImpulse,thrust,duration,initialMass] at *
  constructor <;> linarith

end GNC.Orion.Propulsion
