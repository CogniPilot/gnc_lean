import GNC.Applications.OrbitalFuel.ComparatorReserve

/-! Independently pointed burns satisfy the same physical terminal tolerances.
The signed robust program bounds the retained response. The comparator's
proved continuous region supplies its full nonlinear gravity reserve.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.IndependentTerminalSafety
open GNC SharedBias Matrix PolynomialOrbit Set
open ChaserReferenceData ChaserExistence

def commands (x : Fin 18 → ℝ) (q : Fin 18 → Vec3) (j : Fin 18) : Vec3 :=
  x j • rotate (SharedBiasGeometry.cycleRotation j) (q j)

def response (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Fin 18 → Vec3) : Fin 6 → ℝ :=
  ValidatedSolarFuel.physicalFree z F H+
    ∑ j : Fin 18, BurnSensitivity.physicalMatrix (z (3/5)) (F (3/5)) (H (3/5))
      SolarSensitivityFuel.speed (BurnSensitivity.means z F H j) *ᵥ commands x q j

theorem signed_response (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Fin 18 → Vec3) (i : Fin 12) :
    (∑ j : Fin 18, x j*(BurnSensitivity.physicalH z F H i j ⬝ᵥ q j)) =
      (if i.val%2 = 0 then -1 else 1)*
        (response z F H x q ⟨i.val/2,by omega⟩-
          ValidatedSolarFuel.physicalFree z F H ⟨i.val/2,by omega⟩) := by
  simp_rw [SolarTerminalSafety.command_pairing]
  rw [← Finset.mul_sum]
  congr 1
  simp only [response,Pi.add_apply,Finset.sum_apply]
  change _ = _+(∑ j : Fin 18, _)-_
  abel

theorem retained_box (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (hx : IndependentFeasible SharedBiasExample.axis SharedBiasCertificates.Solar.kappa
      (BurnSensitivity.physicalH z F H) (ValidatedSolarFuel.physicalB z F H) x) (i : Fin 6) :
    |response z F H x q i| ≤ FreeResponse.beta i := by
  have hlo := hx ⟨2*i.val,by omega⟩ q hq
  have hhi := hx ⟨2*i.val+1,by omega⟩ q hq
  rw [signed_response] at hlo hhi
  fin_cases i <;> norm_num [ValidatedSolarFuel.physicalB] at hlo hhi ⊢ <;>
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The stored comparator meets the original six tolerances for every
independent choice of one admissible direction per burn. -/
theorem terminal_box (r : Flow) (q : Fin 18 → Vec3)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (m : Motion r (ComparatorPrefix.commands q)) :
    ExistingSolarCertificate.TerminalBox r (ComparatorPrefix.commands q) m := by
  let z := fun t => lift (r.w t)
  have hx := ValidatedSolarComparator.physical_reference_feasible r.w r.F r.H r.hw r.hF r.hH
    r.hr r.hdw r.hdF r.hdH r.hiw r.hiF r.hiH
  have he := TerminalResponse.nonlinear_endpoint r.w m.p m.v r.F r.H (ComparatorPrefix.commands q)
    SolarSensitivityFuel.speed (Real.sqrt (3/2)) r.hw m.hp m.hv (lift_continuous r.hw r.hr)
    r.hF r.hH (fun t _ => r.hr t) m.noncollision r.hdw r.hdF r.hdH r.hiF r.hiH
    m.initialPlane m.initialNormal m.position_derivative (by
      simpa only [ChaserReferenceData.acceleration,RetainedPrefix.beta,Rat.cast_mul,Rat.cast_ofNat]
        using m.velocity_derivative)
  change _ = response z r.F r.H SolarComparator.plan q+_ at he
  intro i
  rw [show TerminalResponse.output (lift (r.w (3/5))) SolarSensitivityFuel.speed
      (PlanarChaserError.plane (r.w (3/5)) (m.p (3/5)) (m.v (3/5)))
      (PlanarChaserError.normal (m.p (3/5)) (m.v (3/5))) i = _ from congrFun he i,
    Pi.add_apply]
  have h := add_le_add (retained_box z r.F r.H SolarComparator.plan q hq hx i)
    (ComparatorPrefix.gravity_correction r q hq m i)
  exact (abs_add_le _ _).trans (by linarith)

end GNC.Applications.OrbitalFuel.IndependentTerminalSafety
