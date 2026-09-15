import GNC.Applications.OrbitalFuel.SolarPropulsion

/-! The actual solar chaser in SI units with an existing positive mass
schedule and bounded vector thrust. Fuel is the mass lost by this schedule.
The contract uses ideal throttle switching and the prescribed thrust direction;
it does not provide an attitude controller or finite throttle-rate guarantee.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.SolarPropulsion
open GNC PolynomialOrbit Set
open ChaserReferenceData ChaserExistence ExistingSolarCertificate

structure Contract (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (m : Motion r (IndependentTerminalSafety.commands y q)) : Prop where
  continuous_mass : Continuous (mass y)
  initial_mass : mass y 0 = 500
  bounded_mass : ∀ s, 0 < mass y s ∧ mass y s ≤ 500
  bounded_thrust : ∀ k s, GNC.enorm (force r y q k s) ≤ 1/20
  continuous_position : Continuous (PhysicalScaling.position length timeScale m.p)
  continuous_velocity : Continuous (PhysicalScaling.velocity length timeScale m.v)
  nonsingular : ∀ s, s/timeScale ∈ Icc (0:ℝ) (3/5) →
    PhysicalScaling.position length timeScale m.p s ≠ 0
  kinematics : ∀ k < 37, ∀ s, s/timeScale ∈ Ioo (nodes k) (nodes (k+1)) →
    HasDerivAt (PhysicalScaling.position length timeScale m.p)
      (PhysicalScaling.velocity length timeScale m.v s) s
  dynamics : ∀ k < 37, ∀ s, s/timeScale ∈ Ioo (nodes k) (nodes (k+1)) →
    HasDerivAt (PhysicalScaling.velocity length timeScale m.v)
      (Gravity.field3 mu (PhysicalScaling.position length timeScale m.p s)+
        (mass y s)⁻¹ • force r y q k s) s
  flow : ∀ k < 37, ∀ s, s/timeScale ∈ Ioo (nodes k) (nodes (k+1)) →
    HasDerivAt (mass y) (-GNC.enorm (force r y q k s)/exhaust) s
  fuel : 500-mass y (timeScale*(3/5)) = Propellant.consumedMass 500 exhaust
    (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y)

/-- All mass, thrust-magnitude and SI dynamic obligations follow from the
already constructed physical motion and unit-box burn magnitudes. -/
theorem contract (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (m : Motion r (IndependentTerminalSafety.commands y q)) : Contract r y q m := by
  have hdom (k : ℕ) (hk : k < 37) (s : ℝ)
      (hs : s/timeScale ∈ Ioo (nodes k) (nodes (k+1))) :
      s/timeScale ∈ Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ) := by
    simpa only [nodes_eq k (by omega),nodes_eq (k+1) (by omega)] using hs
  refine ⟨PulsePropellant.mass_continuous nodes (amplitude y) 37 timeScale 500 exhaust,
    PulsePropellant.initial_mass nodes (amplitude y) 37 timeScale 500 exhaust nodes_monotone nodes_zero,
    mass_bounds y hy,force_limit r y q hy hq,?_,?_,?_,?_,?_,mass_flow r y q hy hq,
    terminal_consumption y⟩
  · exact (m.hp.comp (continuous_id.div_const timeScale)).const_smul length
  · exact (m.hv.comp (continuous_id.div_const timeScale)).const_smul (length/timeScale)
  · intro s hs
    exact PhysicalScaling.position_nonzero length_pos.ne' (m.noncollision _ hs)
  · intro k hk s hs
    exact PhysicalScaling.position_derivative (m.position_derivative k hk _ (hdom k hk s hs))
  · intro k hk s hs
    have h := PhysicalScaling.velocity_derivative length_pos scaling
      (m.velocity_derivative k hk _ (hdom k hk s hs))
    change HasDerivAt _ (Gravity.field3 mu (PhysicalScaling.position length timeScale m.p s)+
      accelerationScale • acceleration r (IndependentTerminalSafety.commands y q) k (s/timeScale)) s at h
    rw [← acceleration_matches] at h
    simpa only [force,PhysicalScaling.force_recovers_acceleration _ (mass_bounds y hy s).1.ne'] using h

/-- Both existing nonlinear terminal-certified plans have positive mass and
bounded ideal-throttle realizations. The fuel comparison concerns the actual
mass lost by those schedules under the stated exhaust-speed law. -/
theorem exists_propulsion_comparison : ∃ r : Flow,
    ReferenceFlowExistence.CertifiedProgram r ∧
    (∀ q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa,
      ∃ m : Motion r (RetainedPhysical.commands q),
        TerminalBox r (RetainedPhysical.commands q) m ∧
        Contract r SharedBiasCertificates.Solar.x (fun _ => q) m) ∧
    (∀ q : Fin 18 → Vec3,
      (∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) →
      ∃ m : Motion r (ComparatorPrefix.commands q),
        TerminalBox r (ComparatorPrefix.commands q) m ∧ Contract r SolarComparator.plan q m) := by
  obtain ⟨r,hprogram,hcandidate,hcomparison⟩ := CertifiedSolarComparison.exists_certified_comparison
  refine ⟨r,hprogram,?_,?_⟩
  · intro q hq
    obtain ⟨m,hm⟩ := hcandidate q hq
    exact ⟨m,hm,contract r SharedBiasCertificates.Solar.x (fun _ => q)
      SharedBiasCertificates.Solar.in_box (fun _ => hq) m⟩
  · intro q hq
    obtain ⟨m,hm⟩ := hcomparison q hq
    exact ⟨m,hm,contract r SolarComparator.plan q SolarComparator.in_box hq m⟩

/-- The percentage refers to the mass lost by the explicit schedules, with
the exact physical time and exhaust-speed conversion. -/
theorem realized_fuel_saving (r : Flow) (hr : ReferenceFlowExistence.CertifiedProgram r)
    (y : Fin 18 → ℝ)
    (hy : SharedBias.IndependentFeasible SharedBiasExample.axis SharedBiasCertificates.Solar.kappa
      (ReferenceFlowExistence.coefficients r) (ReferenceFlowExistence.budgets r) y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    500-mass SharedBiasCertificates.Solar.x (timeScale*(3/5)) <
      (99/100:ℝ)*(500-mass y (timeScale*(3/5))) := by
  rw [terminal_consumption,terminal_consumption]
  exact (hr.2.2.2 y hy hbox).2

end GNC.Applications.OrbitalFuel.SolarPropulsion
