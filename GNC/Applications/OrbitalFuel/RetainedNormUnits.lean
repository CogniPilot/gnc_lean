import GNC.Applications.OrbitalFuel.RetainedNormData
import GNC.Applications.OrbitalFuel.SolarSensitivityFuel
import GNC.Applications.OrbitalFuel.ValidatedTerminalData

/-! The polynomial-family bounds use the same cap and candidate metadata as
the solar fuel certificate, and the exact physical SI speed conversion.
This is a units/metadata correspondence, not the remaining proof that the
polynomial columns approximate the actual retained dynamical response.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedNorm
open GNC GNC.ThrustSupport RetainedNormData

theorem kappa_matches : (kappa:ℝ) = SharedBiasCertificates.Solar.kappa := by
  norm_num [kappa, SharedBiasCertificates.Solar.kappa]

theorem candidate_matches (i : Fin 18) :
    (fractions i:ℝ) = SharedBiasCertificates.Solar.x i := by
  fin_cases i <;> norm_num [fractions, SharedBiasCertificates.Solar.x]

theorem speed_upper : SolarSensitivityFuel.speed ≤ (speedUpper:ℝ) := by
  have h := (abs_le.mp TerminalData.speed_enclosure).2
  have hu : (speedUpper:ℝ) = (TerminalData.speedCenter:ℝ)+(1/10^25:ℝ) := by
    norm_num [speedUpper, TerminalData.speedCenter]
  rw [hu]
  change Real.sqrt (TerminalData.speedSquared:ℝ) ≤ _
  linarith

/-- Bounds for the polynomial family after exact physical unit conversion.
They include nominal approach motion, not only deviations from that motion. -/
theorem enclosure_si {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) (3/5)) (q : Vec3)
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    ∃ i : Fin 68, t ∈ Set.Icc ((pieces i).start:ℝ) ((pieces i).finish:ℝ) ∧
      GNC.enorm ((lengthScale:ℝ) • (pieces i).response 0 t q) ≤ 10123000 ∧
      GNC.enorm (SolarSensitivityFuel.speed • (pieces i).response 1 t q) ≤ 128/25 := by
  have hq' : q ∈ Cap pointingAxis (kappa:ℝ) := by
    rw [kappa_matches]
    exact hq
  obtain ⟨i,hi,hb⟩ := RetainedNormData.enclosure ht q hq'
  refine ⟨i,hi,?_,?_⟩
  · rw [enorm_smul, abs_of_nonneg (show (0:ℝ) ≤ (lengthScale:ℝ) by norm_num [lengthScale]), mul_comm]
    simpa only [scale, bound, positionBound, Matrix.cons_val_zero] using hb 0
  · rw [enorm_smul, abs_of_nonneg SolarSensitivityFuel.speed_pos.le, mul_comm]
    have h := (mul_le_mul_of_nonneg_left speed_upper (enorm_nonneg ((pieces i).response 1 t q))).trans
      (show GNC.enorm ((pieces i).response 1 t q)*(speedUpper:ℝ) ≤ (velocityBound:ℝ) from hb 1)
    norm_num only [velocityBound, Rat.cast_div, Rat.cast_ofNat] at h
    exact h

end GNC.Applications.OrbitalFuel.RetainedNorm
