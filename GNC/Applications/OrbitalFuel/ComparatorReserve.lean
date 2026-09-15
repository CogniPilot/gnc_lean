import GNC.Applications.OrbitalFuel.ComparatorRegion

/-! The independent comparator's full nonlinear gravity correction fits
the original terminal reserve. The region is a conclusion of first-exit
closure, and all six time-varying transport gains are reused unchanged.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ComparatorPrefix
open GNC PolynomialOrbit PolynomialOrbitTransition PolynomialBurn Set Matrix
open ChaserReferenceData ChaserExistence TerminalGravity

def normalizedPosition : ℝ := (proposedPosition:ℝ)/(RetainedNorm.lengthScale:ℝ)
def gravityReserve : ℝ := 3*normalizedPosition^2/(7997/10000-normalizedPosition)^4

theorem gravityReserve_nonneg : 0 ≤ gravityReserve := by unfold gravityReserve; positivity
theorem separation : normalizedPosition < (7997/10000:ℝ) := by
  norm_num [normalizedPosition,proposedPosition,RetainedNorm.lengthScale]

theorem normalized_position (p : Vec3)
    (hp : GNC.enorm ((RetainedNorm.lengthScale:ℝ) • p) ≤ (proposedPosition:ℝ)) :
    GNC.enorm p ≤ normalizedPosition := by
  unfold normalizedPosition
  rw [GNC.enorm_smul,abs_of_pos (show (0:ℝ) < (RetainedNorm.lengthScale:ℝ) by
    norm_num [RetainedNorm.lengthScale])] at hp
  exact (le_div_iff₀ (by norm_num [RetainedNorm.lengthScale])).mpr (by simpa [mul_comm] using hp)

theorem transport_fits (i : Fin 6) :
    unitScale SolarSensitivityFuel.speed i*(gain i:ℝ)*gravityReserve ≤ 1-FreeResponse.beta i := by
  have hs : SolarSensitivityFuel.speed ≤ 29785 :=
    RetainedNorm.speed_upper.trans (by norm_num [RetainedNorm.speedUpper])
  have hu : unitScale SolarSensitivityFuel.speed i ≤ unitScale 29785 i := by
    fin_cases i <;> simp [unitScale,FreeResponse.tolerance] <;> linarith
  have hg : (0:ℝ) ≤ (gain i:ℝ) := by fin_cases i <;> norm_num [gain]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu hg) gravityReserve_nonneg
  apply h.trans
  fin_cases i <;> norm_num [unitScale,gain,gravityReserve,normalizedPosition,proposedPosition,
    RetainedNorm.lengthScale,FreeResponse.tolerance,FreeResponse.lengthUnit,
    FreeResponse.beta,FreeResponse.negativeRow,FreeResponse.positiveRow,SharedBiasCertificates.Solar.b,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail]

theorem gravity_correction (r : Flow) (q : Fin 18 → Vec3)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (m : Motion r (commands q)) (i : Fin 6) :
    |TerminalResponse.output (lift (r.w (3/5))) SolarSensitivityFuel.speed
      (ChaserResponse.planeRemainder r.F (fun t => PlanarChaserError.residual (r.w t) (m.p t)))
      (ChaserResponse.normalRemainder r.H (fun t => PlanarChaserError.residual (r.w t) (m.p t))) i| ≤
      1-FreeResponse.beta i := by
  let z := fun t => lift (r.w t)
  have hz : Continuous z := lift_continuous r.hw r.hr
  have hdz := fun t ht => lift_derivative (r.hdw t ht) (r.hr t)
  have hiz : z 0 = ValidatedReference.initial := by
    change lift (r.w 0) = ValidatedReference.initial
    rw [r.hiw]
    norm_num [lift,PolynomialOrbit.radius,ValidatedReference.initial]
    exact ⟨rfl,rfl⟩
  let x := Trajectory.ofFlow z r.F r.H hz r.hF r.hH hdz r.hdF r.hdH hiz r.hiF r.hiH
  have hregion := continuous_region r q hq m
  have hrad (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5)) :
      (7997/10000:ℝ) ≤ PolynomialOrbit.radius (r.w t) :=
    (Reference.physical_solar_annulus r.w r.hw r.hdw r.hiw t ht).1.le
  have hb (t : ℝ) (ht : t ∈ Icc (0:ℝ) (3/5)) :=
    PlanarChaserError.residual_bound (r.w t) (m.p t)
      (normalized_position _ (hregion t ht).le) (hrad t ht) separation
  have hc := PlanarChaserError.residual_continuousOn r.hw.continuousOn m.hp.continuousOn
    (fun t _ => r.hr t) m.noncollision
  exact (remainder_bound x z r.F r.H rfl r.hF r.hH _ hc gravityReserve_nonneg
    SolarSensitivityFuel.speed_pos.le hb i).trans (transport_fits i)

end GNC.Applications.OrbitalFuel.ComparatorPrefix
