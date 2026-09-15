# RDD2 navigation estimator interface freeze (phase P0)

This is the sign-off document for the phase P0 interface freeze of the Lean
estimator track. It lists every exported LogicalData declaration of the eFMI
Production Code block `Vehicles.Rdd2.NavigationEstimator` with its exported
component name, unit and manifest classification, and the first disturbance and
sensor-noise bound constants with provenance. Approving this document freezes
the names and classifications; new fields are appended through the manifest
only (design proposal section 8 decision 6).

The Lean transcription lives under `GNC/Estimation/Eskf/`:

- [Interface.lean](../GNC/Estimation/Eskf/Interface.lean): the six sample
  records, `NavigationEstimate`, `EstimatorStatus`, the `Outputs`, `Tuning` and
  `State` records, the `CorrectionOutcome`, `Source` and `Recovery` code types
  with their integer encodings, the `Classification` enumeration and the
  `manifest` declaration table.
- [Sampling.lean](../GNC/Estimation/Eskf/Sampling.lean): the sampler
  assumptions (IMU period and jitter, packet integration, aiding rates and
  staleness, maximum aiding delay, control-path latency budget).
- [Bounds.lean](../GNC/Estimation/Eskf/Bounds.lean): the disturbance and
  sensor-noise bounds with provenance.

Source of truth for names and classifications:
`modelica_models` artifact
`artifacts/vehicles/rdd2/estimator/Vehicles_Rdd2_NavigationEstimator/ProductionCode/`
(`Vehicles_Rdd2_NavigationEstimator.h`, `manifest.xml`). Code encodings:
`Estimation/StrapdownINS/package.mo`. Units below are the SI unit carried in
the exported name suffix; the exported name is authoritative.

## Correction, source and recovery codes

Integer constants from `package.mo`, modeled as inductive types in
`Interface.lean`.

| Code type | Values (encoding) |
| --- | --- |
| `CorrectionOutcome` | NotAttempted 0, Accepted 1, RejectedNotFinite 2, RejectedGate 3, RejectedFactorization 4, RejectedCovarianceUnusable 5, RejectedTimestamp 6, Reseeded 7 |
| `Source` | None 0, Mocap 1, Gps 2, OpticalFlow 3, Magnetometer 4, Barometer 5 |
| `Recovery` | Nominal 0, CovarianceInflated 1, AidingDivergent 2, Misconfigured 3 |

`status.correctionOutcome` carries `CorrectionOutcome`;
`status.correctionSource` and `status.anchorSource` carry `Source`;
`status.recoveryStage` carries `Recovery`. `CorrectionReseeded = 7`,
`status.reseeded` and `status.reseedCount` are the appended re-seed fields.

## Exported declarations

237 declarations total. Classification matches the manifest causality. The
`previous(...)` state declarations are the eFMI discrete `previous()` snapshots
of the corresponding states and are not modeled as independent fields in the
Lean `State` record.

### Inputs (56)

| # | Exported component | Unit | Classification |
| --- | --- | --- | --- |
| 1 | `reset` | 1 | input |
| 2 | `imu.valid` | 1 | input |
| 3 | `imu.fresh` | 1 | input |
| 4 | `imu.timestamp_s` | s | input |
| 5 | `imu.angularVelocityBodyFlu_rad_s` | rad/s | input |
| 6 | `imu.specificForceBodyFlu_m_s2` | m/s^2 | input |
| 7 | `imu.deltaAngleBodyFlu_rad` | rad | input |
| 8 | `imu.deltaVelocityBodyFlu_m_s` | m/s | input |
| 9 | `imu.deltaPositionBodyFlu_m` | m | input |
| 10 | `imu.deltaQuaternionBodyFlu` | 1 | input |
| 11 | `imu.integrationTime_s` | s | input |
| 12 | `imu.gyroscopeBiasLinearizationBodyFlu_rad_s` | rad/s | input |
| 13 | `imu.accelerometerBiasLinearizationBodyFlu_m_s2` | m/s^2 | input |
| 14 | `imu.deltaRotationGyroscopeBiasJacobian_s` | s | input |
| 15 | `imu.deltaVelocityGyroscopeBiasJacobian_m` | m | input |
| 16 | `imu.deltaVelocityAccelerometerBiasJacobian_s` | s | input |
| 17 | `imu.deltaPositionGyroscopeBiasJacobian_m_s` | m/s | input |
| 18 | `imu.deltaPositionAccelerometerBiasJacobian_s2` | s^2 | input |
| 19 | `mocap.valid` | 1 | input |
| 20 | `mocap.fresh` | 1 | input |
| 21 | `mocap.timestamp_s` | s | input |
| 22 | `mocap.positionWorldEnu_m` | m | input |
| 23 | `mocap.quaternionWorldBody` | 1 | input |
| 24 | `mocap.positionCovarianceWorld_m2` | m^2 | input |
| 25 | `mocap.attitudeCovarianceBody_rad2` | rad^2 | input |
| 26 | `gps.valid` | 1 | input |
| 27 | `gps.fresh` | 1 | input |
| 28 | `gps.positionValid` | 1 | input |
| 29 | `gps.velocityValid` | 1 | input |
| 30 | `gps.timestamp_s` | s | input |
| 31 | `gps.geodetic_deg_m` | deg,m | input |
| 32 | `gps.positionWorldEnu_m` | m | input |
| 33 | `gps.velocityWorldEnu_m_s` | m/s | input |
| 34 | `gps.positionCovarianceWorld_m2` | m^2 | input |
| 35 | `gps.velocityCovarianceWorld_m2_s2` | m^2/s^2 | input |
| 36 | `magnetometer.valid` | 1 | input |
| 37 | `magnetometer.fresh` | 1 | input |
| 38 | `magnetometer.timestamp_s` | s | input |
| 39 | `magnetometer.magneticFieldBodyFlu_T` | T | input |
| 40 | `magnetometer.covarianceBody_T2` | T^2 | input |
| 41 | `barometer.valid` | 1 | input |
| 42 | `barometer.fresh` | 1 | input |
| 43 | `barometer.timestamp_s` | s | input |
| 44 | `barometer.altitudeWorldEnu_m` | m | input |
| 45 | `barometer.variance_m2` | m^2 | input |
| 46 | `opticalFlow.valid` | 1 | input |
| 47 | `opticalFlow.fresh` | 1 | input |
| 48 | `opticalFlow.timestamp_s` | s | input |
| 49 | `opticalFlow.integratedLineOfSight_rad` | rad | input |
| 50 | `opticalFlow.integratedLineOfSightCovariance_rad2` | rad^2 | input |
| 51 | `opticalFlow.integratedGyroscopeBodyFlu_rad` | rad | input |
| 52 | `opticalFlow.integratedGyroscopeCovariance_rad2` | rad^2 | input |
| 53 | `opticalFlow.integrationTime_s` | s | input |
| 54 | `opticalFlow.groundDistance_m` | m | input |
| 55 | `opticalFlow.groundDistanceVariance_m2` | m^2 | input |
| 56 | `opticalFlow.quality` | 1 | input |

### Outputs (44)

| # | Exported component | Unit | Classification |
| --- | --- | --- | --- |
| 57 | `errorCovariance` | 1 | output |
| 58 | `estimatedGyroscopeBias_rad_s` | rad/s | output |
| 59 | `estimatedAccelerometerBias_m_s2` | m/s^2 | output |
| 60 | `navigationCovarianceLocal` | 1 | output |
| 61 | `gyroscopeBiasBodyFlu_rad_s` | rad/s | output |
| 62 | `accelerometerBiasBodyFlu_m_s2` | m/s^2 | output |
| 63 | `barometerBias_m` | m | output |
| 64 | `barometerBiasVariance_m2` | m^2 | output |
| 65 | `terrainAltitudeWorldEnu_m` | m | output |
| 66 | `terrainAltitudeVariance_m2` | m^2 | output |
| 67 | `heightAboveTerrain_m` | m | output |
| 68 | `estimate.valid` | 1 | output |
| 69 | `estimate.timestamp_s` | s | output |
| 70 | `estimate.positionWorldEnu_m` | m | output |
| 71 | `estimate.velocityWorldEnu_m_s` | m/s | output |
| 72 | `estimate.accelerationWorldEnu_m_s2` | m/s^2 | output |
| 73 | `estimate.quaternionWorldBody` | 1 | output |
| 74 | `estimate.rotationWorldBody` | 1 | output |
| 75 | `estimate.eulerRpy_rad` | rad | output |
| 76 | `estimate.angularVelocityBodyFlu_rad_s` | rad/s | output |
| 77 | `estimate.angularVelocityWorldEnu_rad_s` | rad/s | output |
| 78 | `status.initialized` | 1 | output |
| 79 | `status.predictionAccepted` | 1 | output |
| 80 | `status.mocapCorrectionAccepted` | 1 | output |
| 81 | `status.gpsPositionCorrectionAccepted` | 1 | output |
| 82 | `status.gpsVelocityCorrectionAccepted` | 1 | output |
| 83 | `status.magnetometerCorrectionAccepted` | 1 | output |
| 84 | `status.barometerCorrectionAccepted` | 1 | output |
| 85 | `status.terrainCorrectionAccepted` | 1 | output |
| 86 | `status.opticalFlowCorrectionAccepted` | 1 | output |
| 87 | `status.consecutiveRejectedCorrections` | 1 | output |
| 88 | `status.rejectionElapsed_s` | s | output |
| 89 | `status.mocapConsecutiveRejections` | 1 | output |
| 90 | `status.gpsConsecutiveRejections` | 1 | output |
| 91 | `status.opticalFlowConsecutiveRejections` | 1 | output |
| 92 | `status.correctionOutcome` | 1 | output |
| 93 | `status.acceptedCorrectionCount` | 1 | output |
| 94 | `status.correctionSource` | 1 | output |
| 95 | `status.normalizedInnovationSquared` | 1 | output |
| 96 | `status.recoveryStage` | 1 | output |
| 97 | `status.imuPayloadHeld` | 1 | output |
| 98 | `status.anchorSource` | 1 | output |
| 99 | `status.reseeded` | 1 | output |
| 100 | `status.reseedCount` | 1 | output |

### Tunable parameters (40)

| # | Exported component | Unit | Classification |
| --- | --- | --- | --- |
| 101 | `varianceLimits.position_m2` | m^2 | tunable_parameter |
| 102 | `varianceLimits.velocity_m2_s2` | m^2/s^2 | tunable_parameter |
| 103 | `varianceLimits.attitude_rad2` | rad^2 | tunable_parameter |
| 104 | `varianceLimits.gyroscopeBias_rad2_s2` | rad^2/s^2 | tunable_parameter |
| 105 | `varianceLimits.accelerometerBias_m2_s4` | m^2/s^4 | tunable_parameter |
| 106 | `innovationGate` | 1 | tunable_parameter |
| 107 | `covarianceInflateWindow_s` | s | tunable_parameter |
| 108 | `covarianceInflateTimeConstant_s` | s | tunable_parameter |
| 109 | `aidingDivergentWindow_s` | s | tunable_parameter |
| 110 | `aidingStaleTimeout_s` | s | tunable_parameter |
| 111 | `aidingReseedWindow_s` | s | tunable_parameter |
| 112 | `gravityWorldEnu_m_s2` | m/s^2 | tunable_parameter |
| 113 | `initialPositionWorldEnu_m` | m | tunable_parameter |
| 114 | `initialVelocityWorldEnu_m_s` | m/s | tunable_parameter |
| 115 | `initialQuaternionWorldBody` | 1 | tunable_parameter |
| 116 | `initialGyroscopeBiasBodyFlu_rad_s` | rad/s | tunable_parameter |
| 117 | `initialAccelerometerBiasBodyFlu_m_s2` | m/s^2 | tunable_parameter |
| 118 | `initialVariances.position_m2` | m^2 | tunable_parameter |
| 119 | `initialVariances.velocity_m2_s2` | m^2/s^2 | tunable_parameter |
| 120 | `initialVariances.attitude_rad2` | rad^2 | tunable_parameter |
| 121 | `initialVariances.gyroscopeBias_rad2_s2` | rad^2/s^2 | tunable_parameter |
| 122 | `initialVariances.accelerometerBias_m2_s4` | m^2/s^4 | tunable_parameter |
| 123 | `processNoise.gyroscope_rad2_s` | rad^2/s | tunable_parameter |
| 124 | `processNoise.accelerometer_m2_s3` | m^2/s^3 | tunable_parameter |
| 125 | `processNoise.gyroscopeBias_rad2_s3` | rad^2/s^3 | tunable_parameter |
| 126 | `processNoise.accelerometerBias_m2_s5` | m^2/s^5 | tunable_parameter |
| 127 | `opticalFlowGroundNormalWorldEnu` | 1 | tunable_parameter |
| 128 | `opticalFlowGroundPlaneOffset_m` | m | tunable_parameter |
| 129 | `localMagneticFieldWorldEnu_T` | T | tunable_parameter |
| 130 | `maximumAidingDelay_s` | s | tunable_parameter |
| 131 | `minimumOpticalFlowQuality` | 1 | tunable_parameter |
| 132 | `minimumOpticalFlowGroundDistance_m` | m | tunable_parameter |
| 133 | `initialBarometerBias_m` | m | tunable_parameter |
| 134 | `initialBarometerBiasVariance_m2` | m^2 | tunable_parameter |
| 135 | `barometerBiasProcessNoise_m2_s` | m^2/s | tunable_parameter |
| 136 | `barometerBiasCalibrationSamples` | 1 | tunable_parameter |
| 137 | `initialTerrainVariance_m2` | m^2 | tunable_parameter |
| 138 | `terrainProcessNoise_m2_s` | m^2/s | tunable_parameter |
| 139 | `minimumRangeCosTilt` | 1 | tunable_parameter |
| 140 | `samplePeriod` | 1 | tunable_parameter |

### States (95)

| # | Exported component | Unit | Classification |
| --- | --- | --- | --- |
| 141 | `statePosition` | 1 | state |
| 142 | `stateVelocity` | 1 | state |
| 143 | `stateQuaternion` | 1 | state |
| 144 | `stateGyroscopeBias` | 1 | state |
| 145 | `stateAccelerometerBias` | 1 | state |
| 146 | `stateCovariance` | 1 | state |
| 147 | `initialized` | 1 | state |
| 148 | `predictionAccepted` | 1 | state |
| 149 | `mocapCorrectionAccepted` | 1 | state |
| 150 | `gpsPositionCorrectionAccepted` | 1 | state |
| 151 | `gpsVelocityCorrectionAccepted` | 1 | state |
| 152 | `magnetometerCorrectionAccepted` | 1 | state |
| 153 | `barometerCorrectionAccepted` | 1 | state |
| 154 | `opticalFlowCorrectionAccepted` | 1 | state |
| 155 | `barometerBiasInitialized` | 1 | state |
| 156 | `barometerBiasUpdateAccepted` | 1 | state |
| 157 | `barometerBiasCalibrationCount` | 1 | state |
| 158 | `stateBarometerBias_m` | m | state |
| 159 | `stateBarometerBiasVariance_m2` | m^2 | state |
| 160 | `terrainInitialized` | 1 | state |
| 161 | `stateTerrainAltitude_m` | m | state |
| 162 | `stateTerrainVariance_m2` | m^2 | state |
| 163 | `terrainCorrectionAccepted` | 1 | state |
| 164 | `auxiliaryRotationWorldBody` | 1 | state |
| 165 | `auxiliaryPredictedVariance_m2` | m^2 | state |
| 166 | `auxiliaryObservationVariance_m2` | m^2 | state |
| 167 | `auxiliaryInnovationVariance_m2` | m^2 | state |
| 168 | `auxiliaryGain` | 1 | state |
| 169 | `auxiliaryObservation_m` | m | state |
| 170 | `auxiliaryCosTilt` | 1 | state |
| 171 | `consecutiveRejectedCorrections` | 1 | state |
| 172 | `rejectionElapsed_s` | s | state |
| 173 | `mocapRejections` | 1 | state |
| 174 | `gpsRejections` | 1 | state |
| 175 | `opticalFlowRejections` | 1 | state |
| 176 | `recoveryStage` | 1 | state |
| 177 | `correctionOutcome` | 1 | state |
| 178 | `correctionSource` | 1 | state |
| 179 | `acceptedCorrectionCount` | 1 | state |
| 180 | `normalizedInnovationSquared` | 1 | state |
| 181 | `estimateValid` | 1 | state |
| 182 | `reseeded` | 1 | state |
| 183 | `reseedCount` | 1 | state |
| 184 | `anchorSource` | 1 | state |
| 185 | `mocapStale_s` | s | state |
| 186 | `gpsStale_s` | s | state |
| 187 | `opticalFlowStale_s` | s | state |
| 188 | `imuAngularVelocityHeld_rad_s` | rad/s | state |
| 189 | `imuSpecificForceHeld_m_s2` | m/s^2 | state |
| 190 | `imuTimestampHeld_s` | s | state |
| 191 | `imuPayloadHeld` | 1 | state |
| 192 | `mocapTimestampConsumed_s` | s | state |
| 193 | `gpsTimestampConsumed_s` | s | state |
| 194 | `magnetometerTimestampConsumed_s` | s | state |
| 195 | `barometerTimestampConsumed_s` | s | state |
| 196 | `opticalFlowTimestampConsumed_s` | s | state |
| 197 | `barometerBiasTimestampConsumed_s` | s | state |
| 198 | `terrainTimestampConsumed_s` | s | state |
| 200 | `previous(barometerBiasTimestampConsumed_s)` | s | state |
| 201 | `previous(terrainTimestampConsumed_s)` | s | state |
| 202 | `previous(stateQuaternion)` | 1 | state |
| 203 | `previous(stateBarometerBiasVariance_m2)` | m^2 | state |
| 204 | `previous(barometerBiasCalibrationCount)` | 1 | state |
| 205 | `previous(barometerBiasInitialized)` | 1 | state |
| 206 | `previous(stateBarometerBias_m)` | m | state |
| 207 | `previous(stateTerrainVariance_m2)` | m^2 | state |
| 208 | `previous(terrainInitialized)` | 1 | state |
| 209 | `previous(statePosition)` | 1 | state |
| 210 | `previous(stateCovariance)` | 1 | state |
| 211 | `previous(stateTerrainAltitude_m)` | m | state |
| 212 | `previous(opticalFlowTimestampConsumed_s)` | s | state |
| 213 | `previous(barometerTimestampConsumed_s)` | s | state |
| 214 | `previous(magnetometerTimestampConsumed_s)` | s | state |
| 215 | `previous(gpsTimestampConsumed_s)` | s | state |
| 216 | `previous(mocapTimestampConsumed_s)` | s | state |
| 217 | `previous(imuTimestampHeld_s)` | s | state |
| 218 | `previous(imuSpecificForceHeld_m_s2)` | m/s^2 | state |
| 219 | `previous(imuAngularVelocityHeld_rad_s)` | rad/s | state |
| 220 | `previous(opticalFlowStale_s)` | s | state |
| 221 | `previous(gpsStale_s)` | s | state |
| 222 | `previous(mocapStale_s)` | s | state |
| 223 | `previous(anchorSource)` | 1 | state |
| 224 | `previous(opticalFlowRejections)` | 1 | state |
| 225 | `previous(gpsRejections)` | 1 | state |
| 226 | `previous(mocapRejections)` | 1 | state |
| 227 | `previous(rejectionElapsed_s)` | s | state |
| 228 | `previous(consecutiveRejectedCorrections)` | 1 | state |
| 229 | `previous(stateAccelerometerBias)` | 1 | state |
| 230 | `previous(stateGyroscopeBias)` | 1 | state |
| 231 | `previous(stateVelocity)` | 1 | state |
| 232 | `previous(initialized)` | 1 | state |
| 233 | `previous(terrainCorrectionAccepted)` | 1 | state |
| 234 | `previous(acceptedCorrectionCount)` | 1 | state |
| 235 | `previous(reseedCount)` | 1 | state |
| 236 | `previous(barometerBiasUpdateAccepted)` | 1 | state |

### Dependent parameters (1)

| # | Exported component | Unit | Classification |
| --- | --- | --- | --- |
| 199 | `initialTerrainAltitudeWorldEnu_m` | m | dependent_parameter |

### Constants (1)

| # | Exported component | Unit | Classification |
| --- | --- | --- | --- |
| 237 | `clockSamplePeriod1` | 1 | constant |

## Sampler assumptions

From [Sampling.lean](../GNC/Estimation/Eskf/Sampling.lean), RDD2 configuration.

| Assumption | Value | Source |
| --- | --- | --- |
| IMU rate | 800 Hz | `replay.c` `IMU_RATE_HZ` |
| IMU sample period | 1/800 s | derived |
| IMU min/max interval | 1.0e-5 s / 0.02 s | `imu_preintegration.h` `RDD2_IMU_PREINTEGRATION_MIN_DT_S` / `MAX_DT_S` |
| IMU jitter bound | 1/1600 s | declared (no firmware constant) |
| Samples per packet | 8 | `replay.c` `divisor` default |
| Packet integration time | 0.01 s | block `samplePeriod` (decl 140) |
| Packet rate | 100 Hz | derived |
| GNSS rate | 5 Hz | flight0114 stream |
| Optical-flow rate | 34 Hz | flight0114 stream |
| Aiding stale timeout | 0.5 s | block `aidingStaleTimeout_s` (decl 110) |
| Maximum aiding delay | 0.2 s | block `maximumAidingDelay_s` (decl 130) |
| Control-path latency budget | 0.005 s | declared budget (proposal section 10 decision 6) |

## Disturbance and sensor-noise bounds

From [Bounds.lean](../GNC/Estimation/Eskf/Bounds.lean). Primary source:
flight0114.mcap, a 995 s hand-carry (never armed) on cerebri_rdd2
platinum-next, analysed 2026-09-15. Placeholders await a flight campaign.

| Bound | Value | Unit | Placeholder | Provenance |
| --- | --- | --- | --- | --- |
| `gyroRestBias_rad_s` | 0.001 | rad/s | no | flight0114 rest period 0-390 s |
| `gyroBiasWalkEnvelope_rad_s` | 0.013 | rad/s | no | flight0114 walk 390-950 s |
| `accelRestMagnitude_m_s2` | 9.83 | m/s^2 | no | flight0114 rest period |
| `gyroNoiseDensity` | 3.16e-3 | rad/s/sqrt(Hz) | yes | needs Allan variance (replay Qgyro=1e-5) |
| `accelNoiseDensity` | 3.16e-2 | m/s^2/sqrt(Hz) | yes | needs Allan variance (replay Qaccel=1e-3) |
| `gnssHorizontalAccuracyFloor_m` | 0.5 | m | no | navigation_gps.c; flight0114 hacc 0.19-3.9 m |
| `gnssVelocityAccuracyFloor_m_s` | 0.1 | m/s | no | navigation_gps.c; flight0114 aided |
| `gnssVerticalAccuracyFloor_m` | 1.0 | m | yes | flight0114 has no vertical GNSS accuracy |
| `walkingSpeedEnvelope_m_s` | 1.35 | m/s | no | flight0114 GNSS ground speed |
| `unaidedVelocityRamp_m_s2` | 0.5 | m/s^2 | no | flight0114 outage sweep |
| `opticalFlowVelocityNoise_m_s` | 1.0 | m/s | no | flight0114 walk |
| `windDisturbance_m_s` | 0 | m/s | yes | requires an armed flight campaign |
| `thrustDisturbance_N` | 0 | N | yes | requires an armed flight campaign |
