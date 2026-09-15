import GNC.Applications.OrbitalFuel.IndependentTerminalSafety

/-! An existing nonlinear candidate and comparator with the same terminal
tolerances and the certified comparison-program fuel gap. The comparator
allows independent pointing errors; the candidate uses a persistent bias.
This is a prescribed-acceleration certificate, not an actuator, keep-out or
abort certificate, nor a lower bound over all nonlinear feasible missions.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.CertifiedSolarComparison
open GNC PolynomialOrbit Set ChaserReferenceData ChaserExistence ExistingSolarCertificate

theorem exists_certified_comparison : ∃ r : Flow,
    ReferenceFlowExistence.CertifiedProgram r ∧
    (∀ q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa,
      ∃ m : Motion r (RetainedPhysical.commands q),
        TerminalBox r (RetainedPhysical.commands q) m) ∧
    (∀ q : Fin 18 → Vec3,
      (∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) →
      ∃ m : Motion r (ComparatorPrefix.commands q),
        TerminalBox r (ComparatorPrefix.commands q) m) := by
  obtain ⟨r,hprogram,hcandidate⟩ := exists_certified_mission
  refine ⟨r,hprogram,hcandidate,?_⟩
  intro q hq
  obtain ⟨m⟩ := independent_motion_exists r SolarComparator.plan SolarComparator.in_box q hq
  exact ⟨m,IndependentTerminalSafety.terminal_box r q hq m⟩

end GNC.Applications.OrbitalFuel.CertifiedSolarComparison
