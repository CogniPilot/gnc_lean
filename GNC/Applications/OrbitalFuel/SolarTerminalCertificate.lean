import GNC.Applications.OrbitalFuel.SolarTerminalReserve
import GNC.Applications.OrbitalFuel.SolarTerminalSafety
import GNC.Applications.OrbitalFuel.ValidatedSolarComparator

/-! The stored solar fuel-saving candidate meets the nonlinear terminal box.
The theorem derives the continuous region and all six gravity reserves from
the prescribed-acceleration model. Existence, noncollision and faithful
realization of that model remain explicit physical hypotheses.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.SolarTerminalCertificate
open GNC GNC.ThrustSupport PolynomialOrbit PolynomialOrbitTransition RetainedPhysical Matrix Set
set_option autoImplicit false

section Motion
variable (w : ℝ → Fin 4 → ℝ) (p v : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (q : Vec3)
    (hw : Continuous w) (hp : Continuous p) (hv : Continuous v)
    (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < radius (w t))
    (hn : ∀ t ∈ Icc (0:ℝ) (3/5), p t ≠ 0)
    (hdw : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt w
      (physicalRate (PolynomialTransition.alpha:ℝ) (w t)) t)
    (hdF : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (lift (w t))*F t) t)
    (hdH : ∀ t ∈ Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (lift (w t))*H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hip : PlanarChaserError.plane (w 0) (p 0) (v 0) = TerminalResponse.initialPlane (Real.sqrt (3/2)))
    (hin : PlanarChaserError.normal (p 0) (v 0) = TerminalResponse.initialNormal)
    (hdp : ∀ k < 37, ∀ t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt p (v t) t)
    (hdv : ∀ k < 37, ∀ t ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt v (Gravity.field3 1 (p t)+BurnSchedule.input
        (fun j t => ChaserResponse.acceleration (RetainedPrefix.beta:ℝ) (lift (w t)) (commands q j)) k t) t)
    (hq : q ∈ Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)

include hw hp hv hF hH hr hn hdw hdF hdH hiw hiF hiH hip hin hdp hdv hq

theorem gravity_reserve (i : Fin 6) :
    |TerminalResponse.output (lift (w (3/5))) SolarSensitivityFuel.speed
      (ChaserResponse.planeRemainder F (fun t => PlanarChaserError.residual (w t) (p t)))
      (ChaserResponse.normalRemainder H (fun t => PlanarChaserError.residual (w t) (p t))) i| ≤
      1-FreeResponse.beta i := by
  have hall := SolarRegion.continuous_nonlinear_enclosure w p v F H q
    hw hp hv hF hH hr hn hdw hdF hdH hiw hiF hiH hip hin hdp hdv hq
  have hg := SolarTerminalReserve.gravity_correction w p F H hw hp hF hH hr
    hdw hdF hdH hiw hiF hiH
    (fun t ht => (hall t ht).1.trans (by norm_num [SolarRegion.proposedPosition])) i
  exact hg.trans (SolarTerminalReserve.physicalBound_fits i)

/-- Every admissible persistent nozzle direction meets the original six
terminal tolerances, including the complete inverse-square gravity error. -/
theorem terminal_box :
    ∀ i, |TerminalResponse.output (lift (w (3/5))) SolarSensitivityFuel.speed
      (PlanarChaserError.plane (w (3/5)) (p (3/5)) (v (3/5)))
      (PlanarChaserError.normal (p (3/5)) (v (3/5))) i| ≤ 1 := by
  have hx := (ValidatedSolarFuel.physical_reference_certificate w F H hw hF hH hr
    hdw hdF hdH hiw hiF hiH).1
  apply SolarTerminalSafety.nonlinear_terminal_box w p v F H SharedBiasCertificates.Solar.x q
    hw hp hv (lift_continuous hw hr) hF hH (fun t _ => hr t) hn hdw hdF hdH hiF hiH
    hip hin hdp (by
      simpa only [RetainedPrefix.beta, Rat.cast_mul, Rat.cast_ofNat,
        commands, SolarTerminalSafety.commands] using hdv) hq hx
  exact gravity_reserve w p v F H q hw hp hv hF hH hr hn hdw hdF hdH hiw hiF hiH hip hin hdp hdv hq

/-- Terminal containment and the quantitative fuel certificate for the same
candidate. The comparator is the declared independent-burn terminal program;
this is not a lower bound over every nonlinear physically feasible plan. -/
theorem safe_and_less_fuel :
    (∀ i, |TerminalResponse.output (lift (w (3/5))) SolarSensitivityFuel.speed
      (PlanarChaserError.plane (w (3/5)) (p (3/5)) (v (3/5)))
      (PlanarChaserError.normal (p (3/5)) (v (3/5))) i| ≤ 1) ∧
    ∀ y : Fin 18 → ℝ,
      SharedBias.IndependentFeasible SharedBiasExample.axis SharedBiasCertificates.Solar.kappa
        (BurnSensitivity.physicalH (fun t => lift (w t)) F H)
        (ValidatedSolarFuel.physicalB (fun t => lift (w t)) F H) y →
      (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) SharedBiasCertificates.Solar.x <
        (9891/10000:ℝ)*FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) ∧
      Propellant.consumedMass 500 (588399/20)
          (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) SharedBiasCertificates.Solar.x) <
        (99/100:ℝ)*Propellant.consumedMass 500 (588399/20)
          (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) := by
  exact ⟨terminal_box w p v F H q hw hp hv hF hH hr hn hdw hdF hdH hiw hiF hiH hip hin hdp hdv hq,
    (ValidatedSolarFuel.physical_reference_certificate w F H hw hF hH hr
      hdw hdF hdH hiw hiF hiH).2⟩

/-- A single theorem supplies nonlinear safety of the candidate, a concrete
feasible independent-burn comparison plan, and quantitative fuel separation.
Feasibility of the comparison program is proved rather than assumed. -/
theorem safe_and_less_fuel_with_comparator :
    (∀ i, |TerminalResponse.output (lift (w (3/5))) SolarSensitivityFuel.speed
      (PlanarChaserError.plane (w (3/5)) (p (3/5)) (v (3/5)))
      (PlanarChaserError.normal (p (3/5)) (v (3/5))) i| ≤ 1) ∧
    SharedBias.IndependentFeasible SharedBiasExample.axis SharedBiasCertificates.Solar.kappa
      (BurnSensitivity.physicalH (fun t => lift (w t)) F H)
      (ValidatedSolarFuel.physicalB (fun t => lift (w t)) F H) SolarComparator.plan ∧
    (∀ j, 0 ≤ SolarComparator.plan j ∧ SolarComparator.plan j ≤ 1) ∧
    (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) SharedBiasCertificates.Solar.x <
      (9891/10000:ℝ)*FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) SolarComparator.plan) ∧
    Propellant.consumedMass 500 (588399/20)
        (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) SharedBiasCertificates.Solar.x) <
      (99/100:ℝ)*Propellant.consumedMass 500 (588399/20)
        (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) SolarComparator.plan) := by
  have hc := safe_and_less_fuel w p v F H q
    hw hp hv hF hH hr hn hdw hdF hdH hiw hiF hiH hip hin hdp hdv hq
  have hy := ValidatedSolarComparator.physical_reference_feasible w F H
    hw hF hH hr hdw hdF hdH hiw hiF hiH
  exact ⟨hc.1, hy, SolarComparator.in_box, hc.2 SolarComparator.plan hy SolarComparator.in_box⟩

end Motion
end GNC.Applications.OrbitalFuel.SolarTerminalCertificate
