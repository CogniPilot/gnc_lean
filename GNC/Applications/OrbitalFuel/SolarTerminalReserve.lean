import GNC.Applications.OrbitalFuel.TerminalGravityBound
import GNC.Applications.OrbitalFuel.NonlinearRegion

/-! Close the six terminal gravity reserves for the solar common-bias plan.
The continuous nonlinear region supplies the forcing bound; certified
time-varying row integrals supply the terminal transport. Neither bound is
assumed from numerical trajectory samples.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.SolarTerminalReserve
open GNC PolynomialOrbit PolynomialOrbitTransition PolynomialBurn Matrix Set
open TerminalGravity SolarRegion
set_option autoImplicit false

/-- Outward-rounded physical gravity corrections: metres, then m/s. -/
def physicalBound : Fin 6 → ℝ := ![992,881,861,723/1000000,558/1000000,542/1000000]

theorem physicalBound_fits (i : Fin 6) :
    physicalBound i/(FreeResponse.tolerance i:ℝ) ≤ 1-FreeResponse.beta i := by
  fin_cases i <;> norm_num [physicalBound, FreeResponse.tolerance, FreeResponse.beta,
    FreeResponse.negativeRow, FreeResponse.positiveRow, SharedBiasCertificates.Solar.b,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem transport_fits (i : Fin 6) :
    unitScale SolarSensitivityFuel.speed i*(gain i:ℝ)*gravityReserve ≤
      physicalBound i/(FreeResponse.tolerance i:ℝ) := by
  have hs : SolarSensitivityFuel.speed ≤ 29785 :=
    RetainedNorm.speed_upper.trans (by norm_num [RetainedNorm.speedUpper])
  have hu : unitScale SolarSensitivityFuel.speed i ≤ unitScale 29785 i := by
    fin_cases i <;> simp [unitScale, FreeResponse.tolerance] <;> linarith
  have hg : (0:ℝ) ≤ (gain i:ℝ) := by fin_cases i <;> norm_num [gain]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu hg) gravityReserve_nonneg
  apply h.trans
  fin_cases i <;> norm_num [unitScale, gain, gravityReserve, normalizedPosition, proposedPosition,
    RetainedNorm.lengthScale, physicalBound, FreeResponse.tolerance, FreeResponse.lengthUnit,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem gravity_correction (w : ℝ → Fin 4 → ℝ) (p : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hw : Continuous w) (hp : Continuous p) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < radius (w t))
    (hdw : ∀ t ∈ Icc (0:ℝ) (3/5),
      HasDerivAt w (physicalRate (PolynomialTransition.alpha:ℝ) (w t)) t)
    (hdF : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hregion : ∀ t ∈ Icc (0:ℝ) (3/5),
      GNC.enorm ((RetainedNorm.lengthScale:ℝ) • (p t-position (w t))) ≤ proposedPosition)
    (i : Fin 6) :
    |TerminalResponse.output (lift (w (3/5))) SolarSensitivityFuel.speed
      (ChaserResponse.planeRemainder F (fun t => PlanarChaserError.residual (w t) (p t)))
      (ChaserResponse.normalRemainder H (fun t => PlanarChaserError.residual (w t) (p t))) i| ≤
      physicalBound i/(FreeResponse.tolerance i:ℝ) := by
  let z := fun t => lift (w t)
  have hz : Continuous z := lift_continuous hw hr
  have hdz := fun t ht => lift_derivative (hdw t ht) (hr t)
  have hiz : z 0 = ValidatedReference.initial := by
    change lift (w 0) = ValidatedReference.initial
    rw [hiw]
    norm_num [lift, radius, ValidatedReference.initial]
    exact ⟨rfl,rfl⟩
  let x := Trajectory.ofFlow z F H hz hF hH hdz hdF hdH hiz hiF hiH
  have hrad (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5)) : 7997/10000 ≤ radius (w t) :=
    (Reference.physical_solar_annulus w hw hdw hiw t ht).1.le
  have hb (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5)) :=
    PlanarChaserError.residual_bound (w t) (p t)
      (normalized_position _ (hregion t ht)) (hrad t ht) separation
  have hc := PlanarChaserError.residual_continuousOn hw.continuousOn hp.continuousOn
    (fun t _ => hr t)
    (fun t ht => PlanarChaserError.chaser_nonzero (w t) (p t)
      (normalized_position _ (hregion t ht)) (hrad t ht) separation)
  exact (remainder_bound x z F H rfl hF hH _ hc gravityReserve_nonneg
    SolarSensitivityFuel.speed_pos.le hb i).trans (transport_fits i)

end GNC.Applications.OrbitalFuel.SolarTerminalReserve
