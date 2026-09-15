import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! # RDD2 navigation estimator block interface (frozen, phase P0)

Lean transcription of the exported eFMI Production Code block
`Vehicles.Rdd2.NavigationEstimator`, taken field for field from its
`ProductionCode/Vehicles_Rdd2_NavigationEstimator.h` header and the
`ProductionCode/manifest.xml` LogicalData surface in the `modelica_models`
repository. This module is the interface freeze: the names and classifications
are the block's, and new fields (the automatic re-seed status) are appended
through the manifest, matching design proposal section 8 decision 6.

Records are parametric in the scalar carrier `α` so the same interface serves
the exact-real primary definition (`α = ℝ`, proposal section 8 decision 1) and
a later binary32 twin. Vectors are `Fin n → α`, covariance blocks are
`Matrix (Fin m) (Fin n) α`. Every field docstring quotes the exported
LogicalData component name and its unit; the authoritative unit is the unit
suffix carried in that exported name.

Correction, source and recovery codes are the algorithm-independent integer
constants from `Estimation/StrapdownINS/package.mo`; they are modeled as
inductive types with their integer encodings so the ladder automaton can be
reasoned about symbolically while the encoding stays checkable against the
manifest. No filter behaviour is defined here; this is data and classification
only. -/

noncomputable section
open Matrix
namespace GNC.Estimation.Eskf

/-- Vehicle-frame or world-frame vector of `n` scalar components. -/
abbrev Vec (α : Type*) (n : Nat) := Fin n → α

/-- Dense `m × n` block, e.g. a covariance or Jacobian block. -/
abbrev Mat (α : Type*) (m n : Nat) := Matrix (Fin m) (Fin n) α

/-! ## Classification (manifest causality) -/

/-- eFMI LogicalData classification, matching the `manifest.xml` causality
kinds `input`, `output`, `tunable_parameter`, `state`, `dependent_parameter`
and `constant`. Recorded per declaration in `manifest` so the Lean interface
can be checked against the exported block later. -/
inductive Classification
  | input
  | output
  | tunableParameter
  | state
  | dependentParameter
  | const
  deriving DecidableEq, Repr

/-! ## Correction, source and recovery codes

Integer constants from `Estimation/StrapdownINS/package.mo`, exposed through
`Avionics.EstimatorStatus`. -/

/-- Correction outcome code (`status.correctionOutcome`, int32). Encodings from
`package.mo`: `CorrectionNotAttempted = 0` .. `CorrectionRejectedTimestamp = 6`,
and `CorrectionReseeded = 7` (the tick the automatic recovery ladder replaces
the state from a fresh anchor). -/
inductive CorrectionOutcome
  | notAttempted
  | accepted
  | rejectedNotFinite
  | rejectedGate
  | rejectedFactorization
  | rejectedCovarianceUnusable
  | rejectedTimestamp
  | reseeded
  deriving DecidableEq, Repr

/-- Integer encoding of `CorrectionOutcome`, matching the `package.mo`
constants exactly. -/
def CorrectionOutcome.encode : CorrectionOutcome → Int
  | .notAttempted => 0
  | .accepted => 1
  | .rejectedNotFinite => 2
  | .rejectedGate => 3
  | .rejectedFactorization => 4
  | .rejectedCovarianceUnusable => 5
  | .rejectedTimestamp => 6
  | .reseeded => 7

/-- Partial inverse of `CorrectionOutcome.encode`. -/
def CorrectionOutcome.decode : Int → Option CorrectionOutcome
  | 0 => some .notAttempted
  | 1 => some .accepted
  | 2 => some .rejectedNotFinite
  | 3 => some .rejectedGate
  | 4 => some .rejectedFactorization
  | 5 => some .rejectedCovarianceUnusable
  | 6 => some .rejectedTimestamp
  | 7 => some .reseeded
  | _ => none

theorem CorrectionOutcome.decode_encode (c : CorrectionOutcome) :
    CorrectionOutcome.decode c.encode = some c := by cases c <;> rfl

/-- Aiding source code (`status.correctionSource` and `status.anchorSource`,
int32). Encodings from `package.mo`: `SourceNone = 0`, `SourceMocap = 1`,
`SourceGps = 2`, `SourceOpticalFlow = 3`, `SourceMagnetometer = 4`,
`SourceBarometer = 5`. -/
inductive Source
  | none
  | mocap
  | gps
  | opticalFlow
  | magnetometer
  | barometer
  deriving DecidableEq, Repr

/-- Integer encoding of `Source`, matching the `package.mo` constants. -/
def Source.encode : Source → Int
  | .none => 0
  | .mocap => 1
  | .gps => 2
  | .opticalFlow => 3
  | .magnetometer => 4
  | .barometer => 5

/-- Partial inverse of `Source.encode`. -/
def Source.decode : Int → Option Source
  | 0 => some .none
  | 1 => some .mocap
  | 2 => some .gps
  | 3 => some .opticalFlow
  | 4 => some .magnetometer
  | 5 => some .barometer
  | _ => none

theorem Source.decode_encode (s : Source) : Source.decode s.encode = some s := by
  cases s <;> rfl

/-- Recovery-ladder stage code (`status.recoveryStage`, int32). Encodings from
`package.mo`: `RecoveryNominal = 0`, `RecoveryCovarianceInflated = 1`,
`RecoveryAidingDivergent = 2`, `RecoveryMisconfigured = 3`. -/
inductive Recovery
  | nominal
  | covarianceInflated
  | aidingDivergent
  | misconfigured
  deriving DecidableEq, Repr

/-- Integer encoding of `Recovery`, matching the `package.mo` constants. -/
def Recovery.encode : Recovery → Int
  | .nominal => 0
  | .covarianceInflated => 1
  | .aidingDivergent => 2
  | .misconfigured => 3

/-- Partial inverse of `Recovery.encode`. -/
def Recovery.decode : Int → Option Recovery
  | 0 => some .nominal
  | 1 => some .covarianceInflated
  | 2 => some .aidingDivergent
  | 3 => some .misconfigured
  | _ => none

theorem Recovery.decode_encode (r : Recovery) : Recovery.decode r.encode = some r := by
  cases r <;> rfl

/-! ## Sample records (block inputs)

The six aiding/inertial sample records, mirroring `Avionics.ImuSample`,
`MocapSample`, `GpsSample`, `MagnetometerSample`, `BarometerSample` and
`OpticalFlowSample`. Field names quote the exported `imu.*`, `mocap.*`,
`gps.*`, `magnetometer.*`, `barometer.*`, `opticalFlow.*` LogicalData paths. -/

/-- IMU sample and preintegrated packet (`imu.*`, block declarations 2-18). -/
structure ImuSample (α : Type*) where
  /-- `imu.valid` (1). -/
  valid : Bool
  /-- `imu.fresh` (1). -/
  fresh : Bool
  /-- `imu.timestamp_s` (s). -/
  timestamp_s : α
  /-- `imu.angularVelocityBodyFlu_rad_s` (rad/s). -/
  angularVelocityBodyFlu_rad_s : Vec α 3
  /-- `imu.specificForceBodyFlu_m_s2` (m/s^2). -/
  specificForceBodyFlu_m_s2 : Vec α 3
  /-- `imu.deltaAngleBodyFlu_rad` (rad). -/
  deltaAngleBodyFlu_rad : Vec α 3
  /-- `imu.deltaVelocityBodyFlu_m_s` (m/s). -/
  deltaVelocityBodyFlu_m_s : Vec α 3
  /-- `imu.deltaPositionBodyFlu_m` (m). -/
  deltaPositionBodyFlu_m : Vec α 3
  /-- `imu.deltaQuaternionBodyFlu` (1). -/
  deltaQuaternionBodyFlu : Vec α 4
  /-- `imu.integrationTime_s` (s). -/
  integrationTime_s : α
  /-- `imu.gyroscopeBiasLinearizationBodyFlu_rad_s` (rad/s). -/
  gyroscopeBiasLinearizationBodyFlu_rad_s : Vec α 3
  /-- `imu.accelerometerBiasLinearizationBodyFlu_m_s2` (m/s^2). -/
  accelerometerBiasLinearizationBodyFlu_m_s2 : Vec α 3
  /-- `imu.deltaRotationGyroscopeBiasJacobian_s` (s). -/
  deltaRotationGyroscopeBiasJacobian_s : Mat α 3 3
  /-- `imu.deltaVelocityGyroscopeBiasJacobian_m` (m). -/
  deltaVelocityGyroscopeBiasJacobian_m : Mat α 3 3
  /-- `imu.deltaVelocityAccelerometerBiasJacobian_s` (s). -/
  deltaVelocityAccelerometerBiasJacobian_s : Mat α 3 3
  /-- `imu.deltaPositionGyroscopeBiasJacobian_m_s` (m/s). -/
  deltaPositionGyroscopeBiasJacobian_m_s : Mat α 3 3
  /-- `imu.deltaPositionAccelerometerBiasJacobian_s2` (s^2). -/
  deltaPositionAccelerometerBiasJacobian_s2 : Mat α 3 3

/-- Motion-capture pose sample (`mocap.*`, block declarations 19-25). -/
structure MocapSample (α : Type*) where
  /-- `mocap.valid` (1). -/
  valid : Bool
  /-- `mocap.fresh` (1). -/
  fresh : Bool
  /-- `mocap.timestamp_s` (s). -/
  timestamp_s : α
  /-- `mocap.positionWorldEnu_m` (m). -/
  positionWorldEnu_m : Vec α 3
  /-- `mocap.quaternionWorldBody` (1). -/
  quaternionWorldBody : Vec α 4
  /-- `mocap.positionCovarianceWorld_m2` (m^2). -/
  positionCovarianceWorld_m2 : Mat α 3 3
  /-- `mocap.attitudeCovarianceBody_rad2` (rad^2). -/
  attitudeCovarianceBody_rad2 : Mat α 3 3

/-- GNSS sample (`gps.*`, block declarations 26-35). -/
structure GpsSample (α : Type*) where
  /-- `gps.valid` (1). -/
  valid : Bool
  /-- `gps.fresh` (1). -/
  fresh : Bool
  /-- `gps.positionValid` (1). -/
  positionValid : Bool
  /-- `gps.velocityValid` (1). -/
  velocityValid : Bool
  /-- `gps.timestamp_s` (s). -/
  timestamp_s : α
  /-- `gps.geodetic_deg_m` (deg, deg, m). -/
  geodetic_deg_m : Vec α 3
  /-- `gps.positionWorldEnu_m` (m). -/
  positionWorldEnu_m : Vec α 3
  /-- `gps.velocityWorldEnu_m_s` (m/s). -/
  velocityWorldEnu_m_s : Vec α 3
  /-- `gps.positionCovarianceWorld_m2` (m^2). -/
  positionCovarianceWorld_m2 : Mat α 3 3
  /-- `gps.velocityCovarianceWorld_m2_s2` (m^2/s^2). -/
  velocityCovarianceWorld_m2_s2 : Mat α 3 3

/-- Magnetometer sample (`magnetometer.*`, block declarations 36-40). -/
structure MagnetometerSample (α : Type*) where
  /-- `magnetometer.valid` (1). -/
  valid : Bool
  /-- `magnetometer.fresh` (1). -/
  fresh : Bool
  /-- `magnetometer.timestamp_s` (s). -/
  timestamp_s : α
  /-- `magnetometer.magneticFieldBodyFlu_T` (T). -/
  magneticFieldBodyFlu_T : Vec α 3
  /-- `magnetometer.covarianceBody_T2` (T^2). -/
  covarianceBody_T2 : Mat α 3 3

/-- Barometer sample (`barometer.*`, block declarations 41-45). -/
structure BarometerSample (α : Type*) where
  /-- `barometer.valid` (1). -/
  valid : Bool
  /-- `barometer.fresh` (1). -/
  fresh : Bool
  /-- `barometer.timestamp_s` (s). -/
  timestamp_s : α
  /-- `barometer.altitudeWorldEnu_m` (m). -/
  altitudeWorldEnu_m : α
  /-- `barometer.variance_m2` (m^2). -/
  variance_m2 : α

/-- Optical-flow sample (`opticalFlow.*`, block declarations 46-56). -/
structure OpticalFlowSample (α : Type*) where
  /-- `opticalFlow.valid` (1). -/
  valid : Bool
  /-- `opticalFlow.fresh` (1). -/
  fresh : Bool
  /-- `opticalFlow.timestamp_s` (s). -/
  timestamp_s : α
  /-- `opticalFlow.integratedLineOfSight_rad` (rad). -/
  integratedLineOfSight_rad : Vec α 2
  /-- `opticalFlow.integratedLineOfSightCovariance_rad2` (rad^2). -/
  integratedLineOfSightCovariance_rad2 : Mat α 2 2
  /-- `opticalFlow.integratedGyroscopeBodyFlu_rad` (rad). -/
  integratedGyroscopeBodyFlu_rad : Vec α 3
  /-- `opticalFlow.integratedGyroscopeCovariance_rad2` (rad^2). -/
  integratedGyroscopeCovariance_rad2 : Mat α 3 3
  /-- `opticalFlow.integrationTime_s` (s). -/
  integrationTime_s : α
  /-- `opticalFlow.groundDistance_m` (m). -/
  groundDistance_m : α
  /-- `opticalFlow.groundDistanceVariance_m2` (m^2). -/
  groundDistanceVariance_m2 : α
  /-- `opticalFlow.quality` (1). -/
  quality : α

/-- All block inputs: the top-level `reset` command and the six sample
records (block declarations 1-56). -/
structure Inputs (α : Type*) where
  /-- `reset` (1). -/
  reset : Bool
  imu : ImuSample α
  mocap : MocapSample α
  gps : GpsSample α
  magnetometer : MagnetometerSample α
  barometer : BarometerSample α
  opticalFlow : OpticalFlowSample α

/-! ## Output records -/

/-- Navigation estimate (`estimate.*`, block declarations 68-77), mirroring
`Avionics.NavigationEstimate`. -/
structure NavigationEstimate (α : Type*) where
  /-- `estimate.valid` (1). -/
  valid : Bool
  /-- `estimate.timestamp_s` (s). -/
  timestamp_s : α
  /-- `estimate.positionWorldEnu_m` (m). -/
  positionWorldEnu_m : Vec α 3
  /-- `estimate.velocityWorldEnu_m_s` (m/s). -/
  velocityWorldEnu_m_s : Vec α 3
  /-- `estimate.accelerationWorldEnu_m_s2` (m/s^2). -/
  accelerationWorldEnu_m_s2 : Vec α 3
  /-- `estimate.quaternionWorldBody` (1). -/
  quaternionWorldBody : Vec α 4
  /-- `estimate.rotationWorldBody` (1). -/
  rotationWorldBody : Mat α 3 3
  /-- `estimate.eulerRpy_rad` (rad). -/
  eulerRpy_rad : Vec α 3
  /-- `estimate.angularVelocityBodyFlu_rad_s` (rad/s). -/
  angularVelocityBodyFlu_rad_s : Vec α 3
  /-- `estimate.angularVelocityWorldEnu_rad_s` (rad/s). -/
  angularVelocityWorldEnu_rad_s : Vec α 3

/-- Estimator status (`status.*`, block declarations 78-100), mirroring
`Avionics.EstimatorStatus`. The integer-coded fields carry the inductive
code types; `reseeded` and `reseedCount` are the appended re-seed fields. -/
structure EstimatorStatus (α : Type*) where
  /-- `status.initialized` (1). -/
  initialized : Bool
  /-- `status.predictionAccepted` (1). -/
  predictionAccepted : Bool
  /-- `status.mocapCorrectionAccepted` (1). -/
  mocapCorrectionAccepted : Bool
  /-- `status.gpsPositionCorrectionAccepted` (1). -/
  gpsPositionCorrectionAccepted : Bool
  /-- `status.gpsVelocityCorrectionAccepted` (1). -/
  gpsVelocityCorrectionAccepted : Bool
  /-- `status.magnetometerCorrectionAccepted` (1). -/
  magnetometerCorrectionAccepted : Bool
  /-- `status.barometerCorrectionAccepted` (1). -/
  barometerCorrectionAccepted : Bool
  /-- `status.terrainCorrectionAccepted` (1). -/
  terrainCorrectionAccepted : Bool
  /-- `status.opticalFlowCorrectionAccepted` (1). -/
  opticalFlowCorrectionAccepted : Bool
  /-- `status.consecutiveRejectedCorrections` (1, count). -/
  consecutiveRejectedCorrections : Int
  /-- `status.rejectionElapsed_s` (s). -/
  rejectionElapsed_s : α
  /-- `status.mocapConsecutiveRejections` (1, count). -/
  mocapConsecutiveRejections : Int
  /-- `status.gpsConsecutiveRejections` (1, count). -/
  gpsConsecutiveRejections : Int
  /-- `status.opticalFlowConsecutiveRejections` (1, count). -/
  opticalFlowConsecutiveRejections : Int
  /-- `status.correctionOutcome` (int32 code). -/
  correctionOutcome : CorrectionOutcome
  /-- `status.acceptedCorrectionCount` (1, count). -/
  acceptedCorrectionCount : Int
  /-- `status.correctionSource` (int32 code). -/
  correctionSource : Source
  /-- `status.normalizedInnovationSquared` (1). -/
  normalizedInnovationSquared : α
  /-- `status.recoveryStage` (int32 code). -/
  recoveryStage : Recovery
  /-- `status.imuPayloadHeld` (1). -/
  imuPayloadHeld : Bool
  /-- `status.anchorSource` (int32 code). -/
  anchorSource : Source
  /-- `status.reseeded` (1). Appended re-seed field. -/
  reseeded : Bool
  /-- `status.reseedCount` (1, count). Appended re-seed field. -/
  reseedCount : Int

/-- All block outputs (block declarations 57-100): standalone covariance and
bias outputs, the terrain outputs, plus the `estimate` and `status` records. -/
structure Outputs (α : Type*) where
  /-- `errorCovariance` (mixed), the 15x15 error-state covariance. -/
  errorCovariance : Mat α 15 15
  /-- `estimatedGyroscopeBias_rad_s` (rad/s). -/
  estimatedGyroscopeBias_rad_s : Vec α 3
  /-- `estimatedAccelerometerBias_m_s2` (m/s^2). -/
  estimatedAccelerometerBias_m_s2 : Vec α 3
  /-- `navigationCovarianceLocal` (mixed), the 6x6 position/velocity block. -/
  navigationCovarianceLocal : Mat α 6 6
  /-- `gyroscopeBiasBodyFlu_rad_s` (rad/s). -/
  gyroscopeBiasBodyFlu_rad_s : Vec α 3
  /-- `accelerometerBiasBodyFlu_m_s2` (m/s^2). -/
  accelerometerBiasBodyFlu_m_s2 : Vec α 3
  /-- `barometerBias_m` (m). -/
  barometerBias_m : α
  /-- `barometerBiasVariance_m2` (m^2). -/
  barometerBiasVariance_m2 : α
  /-- `terrainAltitudeWorldEnu_m` (m). -/
  terrainAltitudeWorldEnu_m : α
  /-- `terrainAltitudeVariance_m2` (m^2). -/
  terrainAltitudeVariance_m2 : α
  /-- `heightAboveTerrain_m` (m). -/
  heightAboveTerrain_m : α
  estimate : NavigationEstimate α
  status : EstimatorStatus α

/-! ## Tunable parameter records (block declarations 101-140)

Split as the block groups them. -/

/-- Per-state covariance ceilings (`varianceLimits.*`). -/
structure VarianceLimits (α : Type*) where
  /-- `varianceLimits.position_m2` (m^2). -/
  position_m2 : Vec α 3
  /-- `varianceLimits.velocity_m2_s2` (m^2/s^2). -/
  velocity_m2_s2 : Vec α 3
  /-- `varianceLimits.attitude_rad2` (rad^2). -/
  attitude_rad2 : Vec α 3
  /-- `varianceLimits.gyroscopeBias_rad2_s2` (rad^2/s^2). -/
  gyroscopeBias_rad2_s2 : Vec α 3
  /-- `varianceLimits.accelerometerBias_m2_s4` (m^2/s^4). -/
  accelerometerBias_m2_s4 : Vec α 3

/-- Initial state-covariance diagonal (`initialVariances.*`). -/
structure InitialVariances (α : Type*) where
  /-- `initialVariances.position_m2` (m^2). -/
  position_m2 : Vec α 3
  /-- `initialVariances.velocity_m2_s2` (m^2/s^2). -/
  velocity_m2_s2 : Vec α 3
  /-- `initialVariances.attitude_rad2` (rad^2). -/
  attitude_rad2 : Vec α 3
  /-- `initialVariances.gyroscopeBias_rad2_s2` (rad^2/s^2). -/
  gyroscopeBias_rad2_s2 : Vec α 3
  /-- `initialVariances.accelerometerBias_m2_s4` (m^2/s^4). -/
  accelerometerBias_m2_s4 : Vec α 3

/-- Continuous process-noise spectral densities (`processNoise.*`). -/
structure ProcessNoise (α : Type*) where
  /-- `processNoise.gyroscope_rad2_s` (rad^2/s). -/
  gyroscope_rad2_s : Mat α 3 3
  /-- `processNoise.accelerometer_m2_s3` (m^2/s^3). -/
  accelerometer_m2_s3 : Mat α 3 3
  /-- `processNoise.gyroscopeBias_rad2_s3` (rad^2/s^3). -/
  gyroscopeBias_rad2_s3 : Mat α 3 3
  /-- `processNoise.accelerometerBias_m2_s5` (m^2/s^5). -/
  accelerometerBias_m2_s5 : Mat α 3 3

/-- Recovery-ladder timing windows, including the re-seed window
(`aidingReseedWindow_s`, appended). -/
structure LadderWindows (α : Type*) where
  /-- `covarianceInflateWindow_s` (s). -/
  covarianceInflateWindow_s : α
  /-- `covarianceInflateTimeConstant_s` (s). -/
  covarianceInflateTimeConstant_s : α
  /-- `aidingDivergentWindow_s` (s). -/
  aidingDivergentWindow_s : α
  /-- `aidingStaleTimeout_s` (s). -/
  aidingStaleTimeout_s : α
  /-- `aidingReseedWindow_s` (s). Appended re-seed window. -/
  aidingReseedWindow_s : α

/-- Initial nominal state (`initial*` tunables, block declarations 113-117). -/
structure InitialState (α : Type*) where
  /-- `initialPositionWorldEnu_m` (m). -/
  initialPositionWorldEnu_m : Vec α 3
  /-- `initialVelocityWorldEnu_m_s` (m/s). -/
  initialVelocityWorldEnu_m_s : Vec α 3
  /-- `initialQuaternionWorldBody` (1). -/
  initialQuaternionWorldBody : Vec α 4
  /-- `initialGyroscopeBiasBodyFlu_rad_s` (rad/s). -/
  initialGyroscopeBiasBodyFlu_rad_s : Vec α 3
  /-- `initialAccelerometerBiasBodyFlu_m_s2` (m/s^2). -/
  initialAccelerometerBiasBodyFlu_m_s2 : Vec α 3

/-- Optical-flow and range geometry constants. -/
structure FlowConstants (α : Type*) where
  /-- `opticalFlowGroundNormalWorldEnu` (1). -/
  opticalFlowGroundNormalWorldEnu : Vec α 3
  /-- `opticalFlowGroundPlaneOffset_m` (m). -/
  opticalFlowGroundPlaneOffset_m : α
  /-- `minimumOpticalFlowQuality` (1). -/
  minimumOpticalFlowQuality : α
  /-- `minimumOpticalFlowGroundDistance_m` (m). -/
  minimumOpticalFlowGroundDistance_m : α
  /-- `minimumRangeCosTilt` (1). -/
  minimumRangeCosTilt : α

/-- Barometer-bias and terrain estimation parameters. -/
structure BarometerTerrainParams (α : Type*) where
  /-- `initialBarometerBias_m` (m). -/
  initialBarometerBias_m : α
  /-- `initialBarometerBiasVariance_m2` (m^2). -/
  initialBarometerBiasVariance_m2 : α
  /-- `barometerBiasProcessNoise_m2_s` (m^2/s). -/
  barometerBiasProcessNoise_m2_s : α
  /-- `barometerBiasCalibrationSamples` (1, count). -/
  barometerBiasCalibrationSamples : Int
  /-- `initialTerrainVariance_m2` (m^2). -/
  initialTerrainVariance_m2 : α
  /-- `terrainProcessNoise_m2_s` (m^2/s). -/
  terrainProcessNoise_m2_s : α

/-- Complete tunable parameter set (block declarations 101-140), split as the
block groups it. `gravityWorldEnu_m_s2`, the innovation gate,
`maximumAidingDelay_s` and `samplePeriod` sit at the top level, matching
`Estimation/StrapdownINS/ESKF/Estimator.mo`. -/
structure Tuning (α : Type*) where
  varianceLimits : VarianceLimits α
  initialVariances : InitialVariances α
  processNoise : ProcessNoise α
  ladder : LadderWindows α
  initialState : InitialState α
  flow : FlowConstants α
  barometerTerrain : BarometerTerrainParams α
  /-- `innovationGate` (1), the per-degree-of-freedom NIS gate. -/
  innovationGate : α
  /-- `gravityWorldEnu_m_s2` (m/s^2). -/
  gravityWorldEnu_m_s2 : Vec α 3
  /-- `localMagneticFieldWorldEnu_T` (T). -/
  localMagneticFieldWorldEnu_T : Vec α 3
  /-- `maximumAidingDelay_s` (s), the maximum accepted aiding-sample delay. -/
  maximumAidingDelay_s : α
  /-- `samplePeriod` (s), the block invocation period (nominal 0.01 s). -/
  samplePeriod : α

/-! ## Filter state record

The semantically distinct filter state (block declarations 141-198). The
`previous(...)` mirror copies (declarations 200-236) are the eFMI discrete
`previous()` snapshots of these same fields and are not modeled as independent
state; `clockSamplePeriod1` (237) is a generated constant. -/

/-- Auxiliary single-tick intermediates the exporter promoted to state
(`auxiliary*`, block declarations 164-170). -/
structure Auxiliary (α : Type*) where
  /-- `auxiliaryRotationWorldBody` (1). -/
  auxiliaryRotationWorldBody : Mat α 3 3
  /-- `auxiliaryPredictedVariance_m2` (m^2). -/
  auxiliaryPredictedVariance_m2 : α
  /-- `auxiliaryObservationVariance_m2` (m^2). -/
  auxiliaryObservationVariance_m2 : α
  /-- `auxiliaryInnovationVariance_m2` (m^2). -/
  auxiliaryInnovationVariance_m2 : α
  /-- `auxiliaryGain` (1). -/
  auxiliaryGain : α
  /-- `auxiliaryObservation_m` (m). -/
  auxiliaryObservation_m : α
  /-- `auxiliaryCosTilt` (1). -/
  auxiliaryCosTilt : α

/-- Discrete recovery-ladder state (block declarations 176-187), the automaton
the flight0114 replay exercised. -/
structure LadderState (α : Type*) where
  /-- `recoveryStage` (int32 code). -/
  recoveryStage : Recovery
  /-- `correctionOutcome` (int32 code). -/
  correctionOutcome : CorrectionOutcome
  /-- `correctionSource` (int32 code). -/
  correctionSource : Source
  /-- `acceptedCorrectionCount` (1, count). -/
  acceptedCorrectionCount : Int
  /-- `normalizedInnovationSquared` (1). -/
  normalizedInnovationSquared : α
  /-- `estimateValid` (1). -/
  estimateValid : Bool
  /-- `reseeded` (1). Appended re-seed field. -/
  reseeded : Bool
  /-- `reseedCount` (1, count). Appended re-seed field. -/
  reseedCount : Int
  /-- `anchorSource` (int32 code). -/
  anchorSource : Source
  /-- `consecutiveRejectedCorrections` (1, count). -/
  consecutiveRejectedCorrections : Int
  /-- `rejectionElapsed_s` (s). -/
  rejectionElapsed_s : α
  /-- `mocapRejections` (1, count). -/
  mocapRejections : Int
  /-- `gpsRejections` (1, count). -/
  gpsRejections : Int
  /-- `opticalFlowRejections` (1, count). -/
  opticalFlowRejections : Int
  /-- `mocapStale_s` (s). -/
  mocapStale_s : α
  /-- `gpsStale_s` (s). -/
  gpsStale_s : α
  /-- `opticalFlowStale_s` (s). -/
  opticalFlowStale_s : α

/-- Complete filter state (block declarations 141-198). -/
structure State (α : Type*) where
  /-- `statePosition` (m), world-ENU position. -/
  statePosition : Vec α 3
  /-- `stateVelocity` (m/s), world-ENU velocity. -/
  stateVelocity : Vec α 3
  /-- `stateQuaternion` (1), world-to-body unit quaternion. -/
  stateQuaternion : Vec α 4
  /-- `stateGyroscopeBias` (rad/s). -/
  stateGyroscopeBias : Vec α 3
  /-- `stateAccelerometerBias` (m/s^2). -/
  stateAccelerometerBias : Vec α 3
  /-- `stateCovariance` (mixed), the 15x15 error-state covariance. -/
  stateCovariance : Mat α 15 15
  /-- `initialized` (1). -/
  initialized : Bool
  /-- `predictionAccepted` (1). -/
  predictionAccepted : Bool
  /-- `mocapCorrectionAccepted` (1). -/
  mocapCorrectionAccepted : Bool
  /-- `gpsPositionCorrectionAccepted` (1). -/
  gpsPositionCorrectionAccepted : Bool
  /-- `gpsVelocityCorrectionAccepted` (1). -/
  gpsVelocityCorrectionAccepted : Bool
  /-- `magnetometerCorrectionAccepted` (1). -/
  magnetometerCorrectionAccepted : Bool
  /-- `barometerCorrectionAccepted` (1). -/
  barometerCorrectionAccepted : Bool
  /-- `opticalFlowCorrectionAccepted` (1). -/
  opticalFlowCorrectionAccepted : Bool
  /-- `barometerBiasInitialized` (1). -/
  barometerBiasInitialized : Bool
  /-- `barometerBiasUpdateAccepted` (1). -/
  barometerBiasUpdateAccepted : Bool
  /-- `barometerBiasCalibrationCount` (1, count). -/
  barometerBiasCalibrationCount : Int
  /-- `stateBarometerBias_m` (m). -/
  stateBarometerBias_m : α
  /-- `stateBarometerBiasVariance_m2` (m^2). -/
  stateBarometerBiasVariance_m2 : α
  /-- `terrainInitialized` (1). -/
  terrainInitialized : Bool
  /-- `stateTerrainAltitude_m` (m). -/
  stateTerrainAltitude_m : α
  /-- `stateTerrainVariance_m2` (m^2). -/
  stateTerrainVariance_m2 : α
  /-- `terrainCorrectionAccepted` (1). -/
  terrainCorrectionAccepted : Bool
  auxiliary : Auxiliary α
  ladder : LadderState α
  /-- `imuAngularVelocityHeld_rad_s` (rad/s). -/
  imuAngularVelocityHeld_rad_s : Vec α 3
  /-- `imuSpecificForceHeld_m_s2` (m/s^2). -/
  imuSpecificForceHeld_m_s2 : Vec α 3
  /-- `imuTimestampHeld_s` (s). -/
  imuTimestampHeld_s : α
  /-- `imuPayloadHeld` (1). -/
  imuPayloadHeld : Bool
  /-- `mocapTimestampConsumed_s` (s). -/
  mocapTimestampConsumed_s : α
  /-- `gpsTimestampConsumed_s` (s). -/
  gpsTimestampConsumed_s : α
  /-- `magnetometerTimestampConsumed_s` (s). -/
  magnetometerTimestampConsumed_s : α
  /-- `barometerTimestampConsumed_s` (s). -/
  barometerTimestampConsumed_s : α
  /-- `opticalFlowTimestampConsumed_s` (s). -/
  opticalFlowTimestampConsumed_s : α
  /-- `barometerBiasTimestampConsumed_s` (s). -/
  barometerBiasTimestampConsumed_s : α
  /-- `terrainTimestampConsumed_s` (s). -/
  terrainTimestampConsumed_s : α

/-! ## Manifest declaration table

Every exported LogicalData declaration with its component name, unit and
classification, generated from the block header `declaration` comments. This
is the machine-checkable record used to check the Lean interface against the
exported `manifest.xml` later. -/

/-- One exported LogicalData declaration. `name` is the exported component
path; `unit` is the SI unit (authoritatively the unit suffix in `name`);
`classification` is the manifest causality. -/
structure FieldSpec where
  index : Nat
  name : String
  unit : String
  classification : Classification
  deriving Repr

/-- The 237 exported declarations of `Vehicles.Rdd2.NavigationEstimator`, in
declaration order. -/
def manifest : List FieldSpec := [
  ⟨1, "reset", "1", .input⟩,
  ⟨2, "imu.valid", "1", .input⟩,
  ⟨3, "imu.fresh", "1", .input⟩,
  ⟨4, "imu.timestamp_s", "s", .input⟩,
  ⟨5, "imu.angularVelocityBodyFlu_rad_s", "rad/s", .input⟩,
  ⟨6, "imu.specificForceBodyFlu_m_s2", "m/s^2", .input⟩,
  ⟨7, "imu.deltaAngleBodyFlu_rad", "rad", .input⟩,
  ⟨8, "imu.deltaVelocityBodyFlu_m_s", "m/s", .input⟩,
  ⟨9, "imu.deltaPositionBodyFlu_m", "m", .input⟩,
  ⟨10, "imu.deltaQuaternionBodyFlu", "1", .input⟩,
  ⟨11, "imu.integrationTime_s", "s", .input⟩,
  ⟨12, "imu.gyroscopeBiasLinearizationBodyFlu_rad_s", "rad/s", .input⟩,
  ⟨13, "imu.accelerometerBiasLinearizationBodyFlu_m_s2", "m/s^2", .input⟩,
  ⟨14, "imu.deltaRotationGyroscopeBiasJacobian_s", "s", .input⟩,
  ⟨15, "imu.deltaVelocityGyroscopeBiasJacobian_m", "m", .input⟩,
  ⟨16, "imu.deltaVelocityAccelerometerBiasJacobian_s", "s", .input⟩,
  ⟨17, "imu.deltaPositionGyroscopeBiasJacobian_m_s", "m/s", .input⟩,
  ⟨18, "imu.deltaPositionAccelerometerBiasJacobian_s2", "s^2", .input⟩,
  ⟨19, "mocap.valid", "1", .input⟩,
  ⟨20, "mocap.fresh", "1", .input⟩,
  ⟨21, "mocap.timestamp_s", "s", .input⟩,
  ⟨22, "mocap.positionWorldEnu_m", "m", .input⟩,
  ⟨23, "mocap.quaternionWorldBody", "1", .input⟩,
  ⟨24, "mocap.positionCovarianceWorld_m2", "m^2", .input⟩,
  ⟨25, "mocap.attitudeCovarianceBody_rad2", "rad^2", .input⟩,
  ⟨26, "gps.valid", "1", .input⟩,
  ⟨27, "gps.fresh", "1", .input⟩,
  ⟨28, "gps.positionValid", "1", .input⟩,
  ⟨29, "gps.velocityValid", "1", .input⟩,
  ⟨30, "gps.timestamp_s", "s", .input⟩,
  ⟨31, "gps.geodetic_deg_m", "deg,m", .input⟩,
  ⟨32, "gps.positionWorldEnu_m", "m", .input⟩,
  ⟨33, "gps.velocityWorldEnu_m_s", "m/s", .input⟩,
  ⟨34, "gps.positionCovarianceWorld_m2", "m^2", .input⟩,
  ⟨35, "gps.velocityCovarianceWorld_m2_s2", "m^2/s^2", .input⟩,
  ⟨36, "magnetometer.valid", "1", .input⟩,
  ⟨37, "magnetometer.fresh", "1", .input⟩,
  ⟨38, "magnetometer.timestamp_s", "s", .input⟩,
  ⟨39, "magnetometer.magneticFieldBodyFlu_T", "T", .input⟩,
  ⟨40, "magnetometer.covarianceBody_T2", "T^2", .input⟩,
  ⟨41, "barometer.valid", "1", .input⟩,
  ⟨42, "barometer.fresh", "1", .input⟩,
  ⟨43, "barometer.timestamp_s", "s", .input⟩,
  ⟨44, "barometer.altitudeWorldEnu_m", "m", .input⟩,
  ⟨45, "barometer.variance_m2", "m^2", .input⟩,
  ⟨46, "opticalFlow.valid", "1", .input⟩,
  ⟨47, "opticalFlow.fresh", "1", .input⟩,
  ⟨48, "opticalFlow.timestamp_s", "s", .input⟩,
  ⟨49, "opticalFlow.integratedLineOfSight_rad", "rad", .input⟩,
  ⟨50, "opticalFlow.integratedLineOfSightCovariance_rad2", "rad^2", .input⟩,
  ⟨51, "opticalFlow.integratedGyroscopeBodyFlu_rad", "rad", .input⟩,
  ⟨52, "opticalFlow.integratedGyroscopeCovariance_rad2", "rad^2", .input⟩,
  ⟨53, "opticalFlow.integrationTime_s", "s", .input⟩,
  ⟨54, "opticalFlow.groundDistance_m", "m", .input⟩,
  ⟨55, "opticalFlow.groundDistanceVariance_m2", "m^2", .input⟩,
  ⟨56, "opticalFlow.quality", "1", .input⟩,
  ⟨57, "errorCovariance", "1", .output⟩,
  ⟨58, "estimatedGyroscopeBias_rad_s", "rad/s", .output⟩,
  ⟨59, "estimatedAccelerometerBias_m_s2", "m/s^2", .output⟩,
  ⟨60, "navigationCovarianceLocal", "1", .output⟩,
  ⟨61, "gyroscopeBiasBodyFlu_rad_s", "rad/s", .output⟩,
  ⟨62, "accelerometerBiasBodyFlu_m_s2", "m/s^2", .output⟩,
  ⟨63, "barometerBias_m", "m", .output⟩,
  ⟨64, "barometerBiasVariance_m2", "m^2", .output⟩,
  ⟨65, "terrainAltitudeWorldEnu_m", "m", .output⟩,
  ⟨66, "terrainAltitudeVariance_m2", "m^2", .output⟩,
  ⟨67, "heightAboveTerrain_m", "m", .output⟩,
  ⟨68, "estimate.valid", "1", .output⟩,
  ⟨69, "estimate.timestamp_s", "s", .output⟩,
  ⟨70, "estimate.positionWorldEnu_m", "m", .output⟩,
  ⟨71, "estimate.velocityWorldEnu_m_s", "m/s", .output⟩,
  ⟨72, "estimate.accelerationWorldEnu_m_s2", "m/s^2", .output⟩,
  ⟨73, "estimate.quaternionWorldBody", "1", .output⟩,
  ⟨74, "estimate.rotationWorldBody", "1", .output⟩,
  ⟨75, "estimate.eulerRpy_rad", "rad", .output⟩,
  ⟨76, "estimate.angularVelocityBodyFlu_rad_s", "rad/s", .output⟩,
  ⟨77, "estimate.angularVelocityWorldEnu_rad_s", "rad/s", .output⟩,
  ⟨78, "status.initialized", "1", .output⟩,
  ⟨79, "status.predictionAccepted", "1", .output⟩,
  ⟨80, "status.mocapCorrectionAccepted", "1", .output⟩,
  ⟨81, "status.gpsPositionCorrectionAccepted", "1", .output⟩,
  ⟨82, "status.gpsVelocityCorrectionAccepted", "1", .output⟩,
  ⟨83, "status.magnetometerCorrectionAccepted", "1", .output⟩,
  ⟨84, "status.barometerCorrectionAccepted", "1", .output⟩,
  ⟨85, "status.terrainCorrectionAccepted", "1", .output⟩,
  ⟨86, "status.opticalFlowCorrectionAccepted", "1", .output⟩,
  ⟨87, "status.consecutiveRejectedCorrections", "1", .output⟩,
  ⟨88, "status.rejectionElapsed_s", "s", .output⟩,
  ⟨89, "status.mocapConsecutiveRejections", "1", .output⟩,
  ⟨90, "status.gpsConsecutiveRejections", "1", .output⟩,
  ⟨91, "status.opticalFlowConsecutiveRejections", "1", .output⟩,
  ⟨92, "status.correctionOutcome", "1", .output⟩,
  ⟨93, "status.acceptedCorrectionCount", "1", .output⟩,
  ⟨94, "status.correctionSource", "1", .output⟩,
  ⟨95, "status.normalizedInnovationSquared", "1", .output⟩,
  ⟨96, "status.recoveryStage", "1", .output⟩,
  ⟨97, "status.imuPayloadHeld", "1", .output⟩,
  ⟨98, "status.anchorSource", "1", .output⟩,
  ⟨99, "status.reseeded", "1", .output⟩,
  ⟨100, "status.reseedCount", "1", .output⟩,
  ⟨101, "varianceLimits.position_m2", "m^2", .tunableParameter⟩,
  ⟨102, "varianceLimits.velocity_m2_s2", "m^2/s^2", .tunableParameter⟩,
  ⟨103, "varianceLimits.attitude_rad2", "rad^2", .tunableParameter⟩,
  ⟨104, "varianceLimits.gyroscopeBias_rad2_s2", "rad^2/s^2", .tunableParameter⟩,
  ⟨105, "varianceLimits.accelerometerBias_m2_s4", "m^2/s^4", .tunableParameter⟩,
  ⟨106, "innovationGate", "1", .tunableParameter⟩,
  ⟨107, "covarianceInflateWindow_s", "s", .tunableParameter⟩,
  ⟨108, "covarianceInflateTimeConstant_s", "s", .tunableParameter⟩,
  ⟨109, "aidingDivergentWindow_s", "s", .tunableParameter⟩,
  ⟨110, "aidingStaleTimeout_s", "s", .tunableParameter⟩,
  ⟨111, "aidingReseedWindow_s", "s", .tunableParameter⟩,
  ⟨112, "gravityWorldEnu_m_s2", "m/s^2", .tunableParameter⟩,
  ⟨113, "initialPositionWorldEnu_m", "m", .tunableParameter⟩,
  ⟨114, "initialVelocityWorldEnu_m_s", "m/s", .tunableParameter⟩,
  ⟨115, "initialQuaternionWorldBody", "1", .tunableParameter⟩,
  ⟨116, "initialGyroscopeBiasBodyFlu_rad_s", "rad/s", .tunableParameter⟩,
  ⟨117, "initialAccelerometerBiasBodyFlu_m_s2", "m/s^2", .tunableParameter⟩,
  ⟨118, "initialVariances.position_m2", "m^2", .tunableParameter⟩,
  ⟨119, "initialVariances.velocity_m2_s2", "m^2/s^2", .tunableParameter⟩,
  ⟨120, "initialVariances.attitude_rad2", "rad^2", .tunableParameter⟩,
  ⟨121, "initialVariances.gyroscopeBias_rad2_s2", "rad^2/s^2", .tunableParameter⟩,
  ⟨122, "initialVariances.accelerometerBias_m2_s4", "m^2/s^4", .tunableParameter⟩,
  ⟨123, "processNoise.gyroscope_rad2_s", "rad^2/s", .tunableParameter⟩,
  ⟨124, "processNoise.accelerometer_m2_s3", "m^2/s^3", .tunableParameter⟩,
  ⟨125, "processNoise.gyroscopeBias_rad2_s3", "rad^2/s^3", .tunableParameter⟩,
  ⟨126, "processNoise.accelerometerBias_m2_s5", "m^2/s^5", .tunableParameter⟩,
  ⟨127, "opticalFlowGroundNormalWorldEnu", "1", .tunableParameter⟩,
  ⟨128, "opticalFlowGroundPlaneOffset_m", "m", .tunableParameter⟩,
  ⟨129, "localMagneticFieldWorldEnu_T", "T", .tunableParameter⟩,
  ⟨130, "maximumAidingDelay_s", "s", .tunableParameter⟩,
  ⟨131, "minimumOpticalFlowQuality", "1", .tunableParameter⟩,
  ⟨132, "minimumOpticalFlowGroundDistance_m", "m", .tunableParameter⟩,
  ⟨133, "initialBarometerBias_m", "m", .tunableParameter⟩,
  ⟨134, "initialBarometerBiasVariance_m2", "m^2", .tunableParameter⟩,
  ⟨135, "barometerBiasProcessNoise_m2_s", "m^2/s", .tunableParameter⟩,
  ⟨136, "barometerBiasCalibrationSamples", "1", .tunableParameter⟩,
  ⟨137, "initialTerrainVariance_m2", "m^2", .tunableParameter⟩,
  ⟨138, "terrainProcessNoise_m2_s", "m^2/s", .tunableParameter⟩,
  ⟨139, "minimumRangeCosTilt", "1", .tunableParameter⟩,
  ⟨140, "samplePeriod", "1", .tunableParameter⟩,
  ⟨141, "statePosition", "1", .state⟩,
  ⟨142, "stateVelocity", "1", .state⟩,
  ⟨143, "stateQuaternion", "1", .state⟩,
  ⟨144, "stateGyroscopeBias", "1", .state⟩,
  ⟨145, "stateAccelerometerBias", "1", .state⟩,
  ⟨146, "stateCovariance", "1", .state⟩,
  ⟨147, "initialized", "1", .state⟩,
  ⟨148, "predictionAccepted", "1", .state⟩,
  ⟨149, "mocapCorrectionAccepted", "1", .state⟩,
  ⟨150, "gpsPositionCorrectionAccepted", "1", .state⟩,
  ⟨151, "gpsVelocityCorrectionAccepted", "1", .state⟩,
  ⟨152, "magnetometerCorrectionAccepted", "1", .state⟩,
  ⟨153, "barometerCorrectionAccepted", "1", .state⟩,
  ⟨154, "opticalFlowCorrectionAccepted", "1", .state⟩,
  ⟨155, "barometerBiasInitialized", "1", .state⟩,
  ⟨156, "barometerBiasUpdateAccepted", "1", .state⟩,
  ⟨157, "barometerBiasCalibrationCount", "1", .state⟩,
  ⟨158, "stateBarometerBias_m", "m", .state⟩,
  ⟨159, "stateBarometerBiasVariance_m2", "m^2", .state⟩,
  ⟨160, "terrainInitialized", "1", .state⟩,
  ⟨161, "stateTerrainAltitude_m", "m", .state⟩,
  ⟨162, "stateTerrainVariance_m2", "m^2", .state⟩,
  ⟨163, "terrainCorrectionAccepted", "1", .state⟩,
  ⟨164, "auxiliaryRotationWorldBody", "1", .state⟩,
  ⟨165, "auxiliaryPredictedVariance_m2", "m^2", .state⟩,
  ⟨166, "auxiliaryObservationVariance_m2", "m^2", .state⟩,
  ⟨167, "auxiliaryInnovationVariance_m2", "m^2", .state⟩,
  ⟨168, "auxiliaryGain", "1", .state⟩,
  ⟨169, "auxiliaryObservation_m", "m", .state⟩,
  ⟨170, "auxiliaryCosTilt", "1", .state⟩,
  ⟨171, "consecutiveRejectedCorrections", "1", .state⟩,
  ⟨172, "rejectionElapsed_s", "s", .state⟩,
  ⟨173, "mocapRejections", "1", .state⟩,
  ⟨174, "gpsRejections", "1", .state⟩,
  ⟨175, "opticalFlowRejections", "1", .state⟩,
  ⟨176, "recoveryStage", "1", .state⟩,
  ⟨177, "correctionOutcome", "1", .state⟩,
  ⟨178, "correctionSource", "1", .state⟩,
  ⟨179, "acceptedCorrectionCount", "1", .state⟩,
  ⟨180, "normalizedInnovationSquared", "1", .state⟩,
  ⟨181, "estimateValid", "1", .state⟩,
  ⟨182, "reseeded", "1", .state⟩,
  ⟨183, "reseedCount", "1", .state⟩,
  ⟨184, "anchorSource", "1", .state⟩,
  ⟨185, "mocapStale_s", "s", .state⟩,
  ⟨186, "gpsStale_s", "s", .state⟩,
  ⟨187, "opticalFlowStale_s", "s", .state⟩,
  ⟨188, "imuAngularVelocityHeld_rad_s", "rad/s", .state⟩,
  ⟨189, "imuSpecificForceHeld_m_s2", "m/s^2", .state⟩,
  ⟨190, "imuTimestampHeld_s", "s", .state⟩,
  ⟨191, "imuPayloadHeld", "1", .state⟩,
  ⟨192, "mocapTimestampConsumed_s", "s", .state⟩,
  ⟨193, "gpsTimestampConsumed_s", "s", .state⟩,
  ⟨194, "magnetometerTimestampConsumed_s", "s", .state⟩,
  ⟨195, "barometerTimestampConsumed_s", "s", .state⟩,
  ⟨196, "opticalFlowTimestampConsumed_s", "s", .state⟩,
  ⟨197, "barometerBiasTimestampConsumed_s", "s", .state⟩,
  ⟨198, "terrainTimestampConsumed_s", "s", .state⟩,
  ⟨199, "initialTerrainAltitudeWorldEnu_m", "m", .dependentParameter⟩,
  ⟨200, "previous(barometerBiasTimestampConsumed_s)", "s", .state⟩,
  ⟨201, "previous(terrainTimestampConsumed_s)", "s", .state⟩,
  ⟨202, "previous(stateQuaternion)", "1", .state⟩,
  ⟨203, "previous(stateBarometerBiasVariance_m2)", "m^2", .state⟩,
  ⟨204, "previous(barometerBiasCalibrationCount)", "1", .state⟩,
  ⟨205, "previous(barometerBiasInitialized)", "1", .state⟩,
  ⟨206, "previous(stateBarometerBias_m)", "m", .state⟩,
  ⟨207, "previous(stateTerrainVariance_m2)", "m^2", .state⟩,
  ⟨208, "previous(terrainInitialized)", "1", .state⟩,
  ⟨209, "previous(statePosition)", "1", .state⟩,
  ⟨210, "previous(stateCovariance)", "1", .state⟩,
  ⟨211, "previous(stateTerrainAltitude_m)", "m", .state⟩,
  ⟨212, "previous(opticalFlowTimestampConsumed_s)", "s", .state⟩,
  ⟨213, "previous(barometerTimestampConsumed_s)", "s", .state⟩,
  ⟨214, "previous(magnetometerTimestampConsumed_s)", "s", .state⟩,
  ⟨215, "previous(gpsTimestampConsumed_s)", "s", .state⟩,
  ⟨216, "previous(mocapTimestampConsumed_s)", "s", .state⟩,
  ⟨217, "previous(imuTimestampHeld_s)", "s", .state⟩,
  ⟨218, "previous(imuSpecificForceHeld_m_s2)", "m/s^2", .state⟩,
  ⟨219, "previous(imuAngularVelocityHeld_rad_s)", "rad/s", .state⟩,
  ⟨220, "previous(opticalFlowStale_s)", "s", .state⟩,
  ⟨221, "previous(gpsStale_s)", "s", .state⟩,
  ⟨222, "previous(mocapStale_s)", "s", .state⟩,
  ⟨223, "previous(anchorSource)", "1", .state⟩,
  ⟨224, "previous(opticalFlowRejections)", "1", .state⟩,
  ⟨225, "previous(gpsRejections)", "1", .state⟩,
  ⟨226, "previous(mocapRejections)", "1", .state⟩,
  ⟨227, "previous(rejectionElapsed_s)", "s", .state⟩,
  ⟨228, "previous(consecutiveRejectedCorrections)", "1", .state⟩,
  ⟨229, "previous(stateAccelerometerBias)", "1", .state⟩,
  ⟨230, "previous(stateGyroscopeBias)", "1", .state⟩,
  ⟨231, "previous(stateVelocity)", "1", .state⟩,
  ⟨232, "previous(initialized)", "1", .state⟩,
  ⟨233, "previous(terrainCorrectionAccepted)", "1", .state⟩,
  ⟨234, "previous(acceptedCorrectionCount)", "1", .state⟩,
  ⟨235, "previous(reseedCount)", "1", .state⟩,
  ⟨236, "previous(barometerBiasUpdateAccepted)", "1", .state⟩,
  ⟨237, "clockSamplePeriod1", "1", .const⟩
]

/-! ## Trivial well-formedness -/

/-- The manifest lists every one of the 237 exported declarations. -/
theorem manifest_length : manifest.length = 237 := by rfl

/-- The error-state covariance is 15x15. -/
theorem covariance_rows : Fintype.card (Fin 15) = 15 := by simp

/-- The attitude state is a four-component quaternion. -/
theorem quaternion_components : Fintype.card (Fin 4) = 4 := by simp

/-- The local navigation covariance output is the 6x6 position/velocity block. -/
theorem navigation_covariance_dim : Fintype.card (Fin 6) = 6 := by simp

end GNC.Estimation.Eskf
