import GNC.Applications.OrbitalFuel.RetainedInitialError

/-! Continuous retained physical-response envelopes for the actual reference,
transition and burn integrals, with the exact initial orbital speed.
The complete transported nonlinear gravity remainder is added separately.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.RetainedPhysical
open GNC GNC.ThrustSupport PolynomialOrbitTransition PolynomialBurn RetainedPrefix Matrix
set_option autoImplicit false

theorem polynomial_error (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hstate : ∀ t, x.state t = pack (z t) (F t) (H t)) (n : Fin 68) {T : ℝ}
    (hT : T ∈ Set.Icc (0:ℝ) (3/5))
    (ht : T ∈ Set.Icc ((RetainedNormData.pieces n).start:ℝ)
      ((RetainedNormData.pieces n).finish:ℝ)) (q : Vec3) (hq : q ⬝ᵥ q = 1) (j : Fin 2) :
    GNC.enorm (retained z F H (Real.sqrt (3/2:ℝ)) q T j-
      (RetainedNormData.pieces n).response j T q) ≤ 5/10^12 := by
  have hc : retained z F H (TerminalData.initialSpeedCenter:ℝ) q T j =
      ValidatedRetainedResponse.response x n T q j := by
    ext i
    exact (response_identity x z F H hz hF hH hstate n hT ht q j i).symm
  have hi := initial_error z F H q T
    (fun i => plane_transition_bound x z F H hstate n ht i 2) j
  rw [hc] at hi
  have he := ValidatedRetainedResponse.response_error x n ht q hq j
  have h := GNC.enorm_add_le
    (retained z F H (Real.sqrt (3/2:ℝ)) q T j-ValidatedRetainedResponse.response x n T q j)
    (ValidatedRetainedResponse.response x n T q j-(RetainedNormData.pieces n).response j T q)
  rw [sub_add_sub_cancel] at h
  linarith

/-- Actual SI retained-response bounds, including the nominal approach
motion, exact burn integrals and initial-root error, at every mission time.
This is not yet a bound on the retained response plus gravity remainder. -/
theorem enclosure_si (x : Trajectory) (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hstate : ∀ t, x.state t = pack (z t) (F t) (H t)) {T : ℝ}
    (hT : T ∈ Set.Icc (0:ℝ) (3/5)) (q : Vec3)
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) • retained z F H (Real.sqrt (3/2:ℝ)) q T 0) ≤ 10123001 ∧
      GNC.enorm (SolarSensitivityFuel.speed • retained z F H (Real.sqrt (3/2:ℝ)) q T 1) ≤
        5120001/1000000 := by
  have hq' : q ∈ Cap pointingAxis (RetainedNorm.kappa:ℝ) := by
    rw [RetainedNorm.kappa_matches]
    exact hq
  obtain ⟨n,hn⟩ := RetainedNormData.coverage hT
  have hb (j : Fin 2) := (RetainedNormData.pieces n).enclosure (RetainedNormData.valid n) j hn q hq'
  have he (j : Fin 2) := polynomial_error x z F H hz hF hH hstate n hT hn q hq.1 j
  have hnorm (j : Fin 2) : GNC.enorm (retained z F H (Real.sqrt (3/2:ℝ)) q T j) ≤
      GNC.enorm ((RetainedNormData.pieces n).response j T q)+5/10^12 := by
    have h := GNC.enorm_add_le
      (retained z F H (Real.sqrt (3/2:ℝ)) q T j-(RetainedNormData.pieces n).response j T q)
      ((RetainedNormData.pieces n).response j T q)
    rw [sub_add_cancel] at h
    linarith [he j]
  constructor
  · rw [GNC.enorm_smul,abs_of_nonneg (by norm_num [RetainedNorm.lengthScale])]
    have h := mul_le_mul_of_nonneg_left (hnorm 0)
      (show (0:ℝ) ≤ (RetainedNorm.lengthScale:ℝ) by norm_num [RetainedNorm.lengthScale])
    have b := hb 0
    norm_num [RetainedNorm.scale,RetainedNorm.bound,RetainedNorm.positionBound,
      RetainedNorm.lengthScale] at b h ⊢
    linarith
  · have hu : (RetainedNorm.speedUpper:ℝ)*GNC.enorm (retained z F H (Real.sqrt (3/2:ℝ)) q T 1) ≤
        5120001/1000000 := by
      have h := mul_le_mul_of_nonneg_left (hnorm 1)
        (show (0:ℝ) ≤ (RetainedNorm.speedUpper:ℝ) by norm_num [RetainedNorm.speedUpper])
      have b := hb 1
      norm_num [RetainedNorm.scale,RetainedNorm.bound,RetainedNorm.velocityBound,
        RetainedNorm.speedUpper] at b h ⊢
      linarith
    rw [GNC.enorm_smul,abs_of_nonneg SolarSensitivityFuel.speed_pos.le]
    exact (mul_le_mul_of_nonneg_right RetainedNorm.speed_upper (GNC.enorm_nonneg _)).trans hu

/-- The representation equality is discharged by constructing the joint
trajectory from the actual reference and fundamental-matrix equations. -/
theorem flow_enclosure (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt z (PolynomialOrbit.rate PolynomialTransition.alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1)
    {T : ℝ} (hT : T ∈ Set.Icc (0:ℝ) (3/5)) (q : Vec3)
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) • retained z F H (Real.sqrt (3/2:ℝ)) q T 0) ≤ 10123001 ∧
      GNC.enorm (SolarSensitivityFuel.speed • retained z F H (Real.sqrt (3/2:ℝ)) q T 1) ≤
        5120001/1000000 :=
  enclosure_si (Trajectory.ofFlow z F H hz hF hH hdz hdF hdH hiz hiF hiH)
    z F H hz hF hH (fun _ => rfl) hT q hq

/-- Specialization to the original inverse-square reference with tangential
thrust, rather than an independently assumed polynomial-state equation. -/
theorem physical_reference_enclosure (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hw : Continuous w) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < PolynomialOrbit.radius (w t))
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt w (PolynomialOrbit.physicalRate PolynomialTransition.alpha (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F
      (planeGenerator (PolynomialOrbit.lift (w t))*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H
      (normalGenerator (PolynomialOrbit.lift (w t))*H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1)
    {T : ℝ} (hT : T ∈ Set.Icc (0:ℝ) (3/5)) (q : Vec3)
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) •
      retained (fun t => PolynomialOrbit.lift (w t)) F H (Real.sqrt (3/2:ℝ)) q T 0) ≤ 10123001 ∧
    GNC.enorm (SolarSensitivityFuel.speed •
      retained (fun t => PolynomialOrbit.lift (w t)) F H (Real.sqrt (3/2:ℝ)) q T 1) ≤ 5120001/1000000 := by
  have hz := PolynomialOrbit.lift_continuous hw hr
  have hdz := fun t ht => PolynomialOrbit.lift_derivative (hdw t ht) (hr t)
  have hiz : PolynomialOrbit.lift (w 0) = ValidatedReference.initial := by
    rw [hiw]
    norm_num [PolynomialOrbit.lift,PolynomialOrbit.radius,ValidatedReference.initial]
    exact ⟨rfl,rfl⟩
  exact flow_enclosure _ F H hz hF hH hdz hdF hdH hiz hiF hiH hT q hq

end GNC.Applications.OrbitalFuel.RetainedPhysical
