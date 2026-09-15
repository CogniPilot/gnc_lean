import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Sampler assumptions for the RDD2 navigation estimator (phase P0)

The sampling model the drift and closed-loop theorems will quantify over,
written as structures with named bounds over `ℝ`. Each field docstring names
its source: a firmware constant (file and name in `cerebri_rdd2`) or a design
proposal decision. Values are the current RDD2 configuration; they are the
frozen assumptions, not derived results.

Model (proposal section 9.2): the IMU runs at 800 Hz and is accumulated into
100 Hz preintegrated packets; aiding sources arrive at their own rates with a
staleness timeout and a maximum accepted delay; the control path is held to a
declared latency budget the firmware asserts against at runtime (proposal
section 10 decision 6). -/

noncomputable section
namespace GNC.Estimation.Eskf

/-- IMU sampling assumptions.

Source: `cerebri_rdd2/tools/log_replay/replay.c` (`IMU_RATE_HZ 800.0f`) and
`tools/log_replay/wiring/imu_preintegration.h`
(`RDD2_IMU_PREINTEGRATION_MIN_DT_S 1.0e-5f`,
`RDD2_IMU_PREINTEGRATION_MAX_DT_S 0.02f`). The preintegrator discards any
inter-sample interval outside `[minInterval_s, maxInterval_s]`; the flight0114
logger rotation dropouts (intervals up to 217 ms) exceed `maxInterval_s` and
are dropped, which is a monitored assumption violation. -/
structure ImuSampling where
  /-- IMU output rate (Hz). `IMU_RATE_HZ = 800`. -/
  rate_Hz : ℝ
  /-- Nominal IMU sample period (s), `1 / rate_Hz`. -/
  samplePeriod_s : ℝ
  /-- Minimum accepted inter-sample interval (s).
  `RDD2_IMU_PREINTEGRATION_MIN_DT_S = 1.0e-5`. -/
  minInterval_s : ℝ
  /-- Maximum accepted inter-sample interval (s).
  `RDD2_IMU_PREINTEGRATION_MAX_DT_S = 0.02`. -/
  maxInterval_s : ℝ
  /-- Assumed bound on IMU timing jitter (s). Proposal decision: a declared
  bound (no dedicated firmware constant); half the nominal period. -/
  jitterBound_s : ℝ

/-- Packet-integration assumptions.

Source: `replay.c` (`efmu.samplePeriod = divisor / IMU_RATE_HZ`, default
`divisor = 8`), giving 100 Hz packets, matching the block tunable
`samplePeriod` (declaration 140). -/
structure PacketIntegration where
  /-- IMU samples accumulated per packet (`divisor`, default 8). -/
  imuSamplesPerPacket : ℝ
  /-- Nominal packet integration time (s), the block `samplePeriod`.
  `8 / 800 = 0.01`. -/
  integrationTime_s : ℝ
  /-- Packet (block invocation) rate (Hz). -/
  packetRate_Hz : ℝ

/-- Aiding-source rate and staleness assumptions.

Source: flight0114 stream rates (`flight0114-estimator-comparison.md`: GNSS
~5 Hz 3D fix, optical flow ~34 Hz) and the block tunables
`aidingStaleTimeout_s` (declaration 110) and `maximumAidingDelay_s`
(declaration 130). -/
structure AidingRates where
  /-- GNSS fix rate (Hz). flight0114: ~5 Hz. -/
  gnssRate_Hz : ℝ
  /-- Optical-flow velocity rate (Hz). flight0114: ~34 Hz. -/
  opticalFlowRate_Hz : ℝ
  /-- Motion-capture rate (Hz). Not present on flight0114; nominal indoor rate.
  Marked provisional. -/
  mocapRate_Hz : ℝ
  /-- Staleness timeout after which an aiding source is treated as unavailable
  (s), block tunable `aidingStaleTimeout_s`. -/
  staleTimeout_s : ℝ
  /-- Maximum accepted aiding-sample delay (s), block tunable
  `maximumAidingDelay_s`; older samples are rejected on timestamp. -/
  maxAidingDelay_s : ℝ

/-- Declared control-path latency budget (proposal section 10 decision 6): the
end-to-end sample-to-actuation latency the sampling theorem (T6) assumes and
the firmware asserts against at runtime, rather than a measured cycle count. -/
structure LatencyBudget where
  /-- Declared sample-to-actuation latency budget (s). -/
  controlPathLatency_s : ℝ

/-- The complete frozen sampler assumption set for RDD2. -/
structure SamplerAssumptions where
  imu : ImuSampling
  packet : PacketIntegration
  aiding : AidingRates
  latency : LatencyBudget

/-- The frozen RDD2 sampler configuration. IMU 800 Hz into 100 Hz packets;
GNSS ~5 Hz, optical flow ~34 Hz; a declared 5 ms control-path latency budget
(proposal section 10 decision 6). Numeric aiding-delay and staleness values
mirror the current `Estimator.mo` tunables. -/
def rdd2Sampler : SamplerAssumptions where
  imu :=
    { rate_Hz := 800
      samplePeriod_s := 1 / 800
      minInterval_s := 1.0e-5
      maxInterval_s := 0.02
      jitterBound_s := 1 / 1600 }
  packet :=
    { imuSamplesPerPacket := 8
      integrationTime_s := 0.01
      packetRate_Hz := 100 }
  aiding :=
    { gnssRate_Hz := 5
      opticalFlowRate_Hz := 34
      mocapRate_Hz := 100
      staleTimeout_s := 0.5
      maxAidingDelay_s := 0.2 }
  latency := { controlPathLatency_s := 0.005 }

/-- The nominal packet integration time is one IMU period times the samples per
packet, consistent with `samplePeriod = divisor / IMU_RATE_HZ`. -/
theorem rdd2_integration_time_consistent :
    rdd2Sampler.packet.integrationTime_s
      = rdd2Sampler.imu.samplePeriod_s * rdd2Sampler.packet.imuSamplesPerPacket := by
  norm_num [rdd2Sampler]

/-- The 100 Hz packet rate is 800 Hz divided by the samples per packet. -/
theorem rdd2_packet_rate_consistent :
    rdd2Sampler.packet.packetRate_Hz
      = rdd2Sampler.imu.rate_Hz / rdd2Sampler.packet.imuSamplesPerPacket := by
  norm_num [rdd2Sampler]

end GNC.Estimation.Eskf
