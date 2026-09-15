import GNC.Applications.OrbitalFuel.ChaserExistence
import GNC.Applications.OrbitalFuel.SolarTerminalCertificate

/-! An existing nonlinear solar chaser with the certified terminal box.
Reference and chaser existence, including avoidance of the gravity singularity,
are conclusions. The cost comparison remains over the declared independent-burn
terminal program. This is not a keep-out, docking, or actuator certificate.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ExistingSolarCertificate
open GNC PolynomialOrbit PolynomialOrbitTransition Set
open ChaserExistence ChaserReferenceData

def TerminalBox (r : Flow) (commands : Fin 18 → Vec3) (m : Motion r commands) : Prop :=
  ∀ i, |TerminalResponse.output (lift (r.w (3/5))) SolarSensitivityFuel.speed
    (PlanarChaserError.plane (r.w (3/5)) (m.p (3/5)) (m.v (3/5)))
    (PlanarChaserError.normal (m.p (3/5)) (m.v (3/5))) i| ≤ 1

/-- Every motion of the stored common-bias plan obeys the nonlinear terminal
tolerances; the flow's hypotheses are supplied by the existence construction. -/
theorem terminal_box (r : Flow) (q : Vec3)
    (hq : q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (m : Motion r (RetainedPhysical.commands q)) :
    TerminalBox r (RetainedPhysical.commands q) m := by
  exact SolarTerminalCertificate.terminal_box r.w m.p m.v r.F r.H q
    r.hw m.hp m.hv r.hF r.hH r.hr m.noncollision r.hdw r.hdF r.hdH
    r.hiw r.hiF r.hiH m.initialPlane m.initialNormal
    m.position_derivative m.velocity_derivative hq

/-- The actual prescribed-acceleration mission exists for every admissible
persistent pointing direction and meets all six terminal tolerances. The same
reference supplies candidate/comparator program feasibility and the universal
strict delta-v and ideal-propellant cost gap in `CertifiedProgram`. -/
theorem exists_certified_mission : ∃ r : Flow,
    ReferenceFlowExistence.CertifiedProgram r ∧
    ∀ q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa,
      ∃ m : Motion r (RetainedPhysical.commands q),
        TerminalBox r (RetainedPhysical.commands q) m := by
  obtain ⟨r⟩ := ReferenceFlowExistence.exists_reference_flow
  refine ⟨r,ReferenceFlowExistence.reference_program_certified r,?_⟩
  intro q hq
  obtain ⟨m⟩ := exists_motion r (RetainedPhysical.commands q) (shared_commands_bound q hq)
  exact ⟨m,terminal_box r q hq m⟩

/-- Independent-burn comparison commands also have actual nonlinear motions.
This establishes existence and avoidance of the gravity singularity, not the
comparison plan's nonlinear terminal reserve or collision/abort constraints. -/
theorem independent_motion_exists (r : Flow) (y : Fin 18 → ℝ)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (q : Fin 18 → Vec3)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    Nonempty (Motion r (fun j => y j • rotate (SharedBiasGeometry.cycleRotation j) (q j))) := by
  apply exists_motion
  intro j
  rw [GNC.enorm_smul,GNC.rotate_enorm,ThrustSupport.unit_enorm _ (hq j).1,
    mul_one,abs_of_nonneg (hy j).1]
  exact (hy j).2

end GNC.Applications.OrbitalFuel.ExistingSolarCertificate
