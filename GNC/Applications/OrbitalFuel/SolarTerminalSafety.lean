import GNC.Applications.OrbitalFuel.TerminalResponse
import GNC.Applications.OrbitalFuel.ValidatedSolarFuel

/-! The signed common-bias fuel constraints imply the retained terminal box.
An explicitly bounded transported remainder then implies the full terminal
tolerance box. The remainder bound is a separate obligation; the nonlinear
endpoint equality supplying it is proved in TerminalResponse.
-/
noncomputable section
open Matrix
namespace GNC.Applications.OrbitalFuel.SolarTerminalSafety
open GNC SharedBias

def commands (x : Fin 18 → ℝ) (q : Vec3) (j : Fin 18) : Vec3 :=
  x j • rotate (SharedBiasGeometry.cycleRotation j) q

def response (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Vec3) : Fin 6 → ℝ :=
  ValidatedSolarFuel.physicalFree z F H+
    ∑ j : Fin 18, BurnSensitivity.physicalMatrix (z (3/5)) (F (3/5)) (H (3/5))
      SolarSensitivityFuel.speed (BurnSensitivity.means z F H j) *ᵥ commands x q j

theorem command_pairing (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Vec3) (i : Fin 12) (j : Fin 18) :
    x j*(BurnSensitivity.physicalH z F H i j ⬝ᵥ q) =
      (if i.val%2 = 0 then -1 else 1)*
        (BurnSensitivity.physicalMatrix (z (3/5)) (F (3/5)) (H (3/5))
          SolarSensitivityFuel.speed (BurnSensitivity.means z F H j) *ᵥ commands x q j)
          ⟨i.val/2,by omega⟩ := by
  let C := BurnSensitivity.physicalMatrix (z (3/5)) (F (3/5)) (H (3/5))
    SolarSensitivityFuel.speed (BurnSensitivity.means z F H j)
  let R := (SharedBiasGeometry.cycleRotation j).val
  let s : ℝ := if i.val%2 = 0 then -1 else 1
  let r : Fin 6 := ⟨i.val/2,by omega⟩
  change x j*((fun k => s*(C*R) r k) ⬝ᵥ q) = s*(C *ᵥ (x j • (R *ᵥ q))) r
  rw [mulVec_smul, mulVec_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem signed_response (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Vec3) (i : Fin 12) :
    combined (BurnSensitivity.physicalH z F H i) x ⬝ᵥ q =
      (if i.val%2 = 0 then -1 else 1)*
        (response z F H x q ⟨i.val/2,by omega⟩-
          ValidatedSolarFuel.physicalFree z F H ⟨i.val/2,by omega⟩) := by
  rw [combined_pairing]
  simp_rw [command_pairing]
  rw [← Finset.mul_sum]
  congr 1
  simp only [response, Pi.add_apply, Finset.sum_apply]
  abel

theorem retained_box (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Vec3)
    (hq : q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (hx : CommonFeasible SharedBiasExample.axis SharedBiasCertificates.Solar.kappa
      (BurnSensitivity.physicalH z F H) (ValidatedSolarFuel.physicalB z F H) x) (i : Fin 6) :
    |response z F H x q i| ≤ FreeResponse.beta i := by
  have hlo := hx ⟨2*i.val,by omega⟩ q hq
  have hhi := hx ⟨2*i.val+1,by omega⟩ q hq
  rw [signed_response] at hlo hhi
  fin_cases i <;> norm_num [ValidatedSolarFuel.physicalB] at hlo hhi ⊢ <;>
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Apply the exact endpoint identity and charge the transported error to
the declared reserve. This implication does not assume a zero remainder. -/
theorem terminal_box (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Vec3)
    (actual error : Fin 6 → ℝ)
    (hq : q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (hx : CommonFeasible SharedBiasExample.axis SharedBiasCertificates.Solar.kappa
      (BurnSensitivity.physicalH z F H) (ValidatedSolarFuel.physicalB z F H) x)
    (he : actual = response z F H x q+error)
    (hr : ∀ i, |error i| ≤ 1-FreeResponse.beta i) : ∀ i, |actual i| ≤ 1 := by
  intro i
  rw [he, Pi.add_apply]
  have h := add_le_add (retained_box z F H x q hq hx i) (hr i)
  exact (abs_add_le _ _).trans (by linarith)

/-- Compose the physical switched ODE, exact terminal-map identity, and
common-bias certificate. Only the transported gravity reserve remains a
terminal error hypothesis; the retained linear error equation is derived.
-/
theorem nonlinear_terminal_box (w : ℝ → Fin 4 → ℝ) (p v : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (x : Fin 18 → ℝ) (q : Vec3)
    (hw : Continuous w) (hp : Continuous p) (hv : Continuous v)
    (hz : Continuous (fun t => PolynomialOrbit.lift (w t))) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t ∈ Set.Icc (0:ℝ) (3/5), 0 < PolynomialOrbit.radius (w t))
    (hn : ∀ t ∈ Set.Icc (0:ℝ) (3/5), p t ≠ 0)
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt w (PolynomialOrbit.physicalRate
      (FreeResponse.alpha:ℝ) (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F
      (PolynomialOrbitTransition.planeGenerator (PolynomialOrbit.lift (w t))*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H
      (PolynomialOrbitTransition.normalGenerator (PolynomialOrbit.lift (w t))*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hip : PlanarChaserError.plane (w 0) (p 0) (v 0) = TerminalResponse.initialPlane (Real.sqrt (3/2)))
    (hin : PlanarChaserError.normal (p 0) (v 0) = TerminalResponse.initialNormal)
    (hdp : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt p (v t) t)
    (hdv : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt v (Gravity.field3 1 (p t)+BurnSchedule.input
        (fun j t => ChaserResponse.acceleration (50*(BurnSensitivity.burnScale:ℝ))
          (PolynomialOrbit.lift (w t)) (commands x q j)) k t) t)
    (hq : q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (hx : CommonFeasible SharedBiasExample.axis SharedBiasCertificates.Solar.kappa
      (BurnSensitivity.physicalH (fun t => PolynomialOrbit.lift (w t)) F H)
      (ValidatedSolarFuel.physicalB (fun t => PolynomialOrbit.lift (w t)) F H) x)
    (hreserve : ∀ i, |TerminalResponse.output (PolynomialOrbit.lift (w (3/5))) SolarSensitivityFuel.speed
      (ChaserResponse.planeRemainder F (fun t => PlanarChaserError.residual (w t) (p t)))
      (ChaserResponse.normalRemainder H (fun t => PlanarChaserError.residual (w t) (p t))) i| ≤
        1-FreeResponse.beta i) :
    ∀ i, |TerminalResponse.output (PolynomialOrbit.lift (w (3/5))) SolarSensitivityFuel.speed
      (PlanarChaserError.plane (w (3/5)) (p (3/5)) (v (3/5)))
      (PlanarChaserError.normal (p (3/5)) (v (3/5))) i| ≤ 1 := by
  have he := TerminalResponse.nonlinear_endpoint w p v F H (commands x q) SolarSensitivityFuel.speed
    (Real.sqrt (3/2)) hw hp hv hz hF hH hr hn hdw hdF hdH hiF hiH hip hin hdp hdv
  exact terminal_box (fun t => PolynomialOrbit.lift (w t)) F H x q _ _ hq hx he hreserve

end GNC.Applications.OrbitalFuel.SolarTerminalSafety
