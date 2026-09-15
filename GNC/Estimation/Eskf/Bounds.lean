import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Disturbance and sensor-noise bounds for the RDD2 estimator (phase P0)

Named bound constants with provenance, the first instantiation of the drift
envelope and closed-loop hypotheses (proposal section 8 decision 5, section 10
decision 5: bounds taken from flight logs, recorded with provenance, revisited
per campaign). Each bound is a `Bound` record carrying its value, unit, a
provenance string (log name, method, date) and a `placeholder` flag. Bounds a
hand-carry log cannot supply (wind, thrust disturbance) are present as
placeholders marked `placeholder := true`.

Primary source: flight0114.mcap, a 995 s hand-carry (never armed) on
cerebri_rdd2 platinum-next, analysed 2026-09-15; write-up
`~/.claude_documents/.../flight0114-estimator-comparison.md`. -/

noncomputable section
namespace GNC.Estimation.Eskf

/-- A named bound with provenance. `value` is in `unit`; `source` records the
log, method and date; `placeholder` is `true` when the value is not yet backed
by data and needs a flight campaign. -/
structure Bound where
  value : ℝ
  unit : String
  source : String
  placeholder : Bool

namespace Bounds

/-- Gyroscope in-run bias magnitude at rest (rad/s). flight0114 rest period
(0-390 s): true bias ~0.001 rad/s. -/
def gyroRestBias_rad_s : Bound :=
  { value := 0.001, unit := "rad/s"
    source := "flight0114.mcap rest period 0-390 s; rest-average of gyro; 2026-09-15"
    placeholder := false }

/-- Gyroscope bias excursion observed while walking (rad/s). flight0114: the
bias states wandered to ~0.013 rad/s (about 10x the rest bias). Used as the
in-flight bias-instability envelope. -/
def gyroBiasWalkEnvelope_rad_s : Bound :=
  { value := 0.013, unit := "rad/s"
    source := "flight0114.mcap walk 390-950 s; observed gyro-bias state excursion; 2026-09-15"
    placeholder := false }

/-- Accelerometer specific-force magnitude at rest (m/s^2), az = +9.83 at rest,
a gravity-magnitude and rest-consistency reference. -/
def accelRestMagnitude_m_s2 : Bound :=
  { value := 9.83, unit := "m/s^2"
    source := "flight0114.mcap rest period; rest-average accelerometer z; 2026-09-15"
    placeholder := false }

/-- Gyroscope noise density (rad/s/sqrt(Hz)). PLACEHOLDER: flight0114 gives the
rest bias but no computed Allan-deviation noise density; the current working
value is the replay process-noise spectral density Qgyro = 1e-5 rad^2/s
(`Estimator.mo` default) restated as a density and must be replaced by an
Allan-variance estimate. -/
def gyroNoiseDensity : Bound :=
  { value := 3.16e-3, unit := "rad/s/sqrt(Hz)"
    source := "PLACEHOLDER: sqrt(Qgyro=1e-5) replay default; needs Allan variance; 2026-09-15"
    placeholder := true }

/-- Accelerometer noise density (m/s^2/sqrt(Hz)). PLACEHOLDER: as
`gyroNoiseDensity`, from the replay Qaccel = 1e-3 m^2/s^3 default; needs an
Allan-variance estimate. -/
def accelNoiseDensity : Bound :=
  { value := 3.16e-2, unit := "m/s^2/sqrt(Hz)"
    source := "PLACEHOLDER: sqrt(Qaccel=1e-3) replay default; needs Allan variance; 2026-09-15"
    placeholder := true }

/-- GNSS horizontal position accuracy floor (m). navigation_gps.c uses a 0.5 m
horizontal floor; flight0114 reported hacc in 0.19-3.9 m. -/
def gnssHorizontalAccuracyFloor_m : Bound :=
  { value := 0.5, unit := "m"
    source := "cerebri_rdd2 navigation_gps.c floor; flight0114 hacc 0.19-3.9 m; 2026-09-15"
    placeholder := false }

/-- GNSS horizontal velocity accuracy floor (m/s). navigation_gps.c uses a
0.1 m/s floor; the aided filter under-reported velocity sigma against it. -/
def gnssVelocityAccuracyFloor_m_s : Bound :=
  { value := 0.1, unit := "m/s"
    source := "cerebri_rdd2 navigation_gps.c floor; flight0114 aided comparison; 2026-09-15"
    placeholder := false }

/-- GNSS vertical position accuracy floor (m). PLACEHOLDER: flight0114 GNSS
carried no vertical velocity and no separate vertical accuracy; taken as twice
the horizontal floor pending a log that measures it. -/
def gnssVerticalAccuracyFloor_m : Bound :=
  { value := 1.0, unit := "m"
    source := "PLACEHOLDER: flight0114 has no vertical GNSS accuracy; 2x horizontal; 2026-09-15"
    placeholder := true }

/-- Walking-pace speed envelope (m/s). flight0114 walk: ~1.35 m/s. The
low-dynamics envelope for the hand-carry regime. -/
def walkingSpeedEnvelope_m_s : Bound :=
  { value := 1.35, unit := "m/s"
    source := "flight0114.mcap walk 390-950 s; GNSS ground speed; 2026-09-15"
    placeholder := false }

/-- Unaided horizontal velocity ramp while walking (m/s^2). flight0114: the
unaided velocity ramps at ~0.5 m/s^2 from the first second of an outage, the
dead-reckoning error-growth envelope. -/
def unaidedVelocityRamp_m_s2 : Bound :=
  { value := 0.5, unit := "m/s^2"
    source := "flight0114.mcap outage sweep; unaided velocity growth; 2026-09-15"
    placeholder := false }

/-- Optical-flow velocity noise at walking pace (m/s). flight0114: ~1 m/s. -/
def opticalFlowVelocityNoise_m_s : Bound :=
  { value := 1.0, unit := "m/s"
    source := "flight0114.mcap walk; flow velocity residual; 2026-09-15"
    placeholder := false }

/-- Horizontal wind disturbance bound (m/s). PLACEHOLDER: flight0114 was a
hand-carry, never armed, so it carries no wind or thrust data; only a flight
campaign can provide this. -/
def windDisturbance_m_s : Bound :=
  { value := 0, unit := "m/s"
    source := "PLACEHOLDER: requires an armed flight campaign; flight0114 is a hand-carry; 2026-09-15"
    placeholder := true }

/-- Thrust/actuator disturbance bound (N). PLACEHOLDER: as `windDisturbance_m_s`;
requires an armed flight campaign. -/
def thrustDisturbance_N : Bound :=
  { value := 0, unit := "N"
    source := "PLACEHOLDER: requires an armed flight campaign; flight0114 is a hand-carry; 2026-09-15"
    placeholder := true }

/-- All bounds in this module, in declaration order. -/
def all : List Bound :=
  [gyroRestBias_rad_s, gyroBiasWalkEnvelope_rad_s, accelRestMagnitude_m_s2,
   gyroNoiseDensity, accelNoiseDensity, gnssHorizontalAccuracyFloor_m,
   gnssVelocityAccuracyFloor_m_s, gnssVerticalAccuracyFloor_m,
   walkingSpeedEnvelope_m_s, unaidedVelocityRamp_m_s2, opticalFlowVelocityNoise_m_s,
   windDisturbance_m_s, thrustDisturbance_N]

/-- The five bounds still awaiting data (two noise densities, the vertical
GNSS floor, wind and thrust) are exactly the ones flagged `placeholder`. -/
theorem placeholder_count : (all.filter (·.placeholder)).length = 5 := by rfl

end Bounds
end GNC.Estimation.Eskf
