import GNC.Applications.OrbitalFuel.SolarAttitudeRealization
import GNC.Control.ReactionWheelAllocation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-! Nominal reaction-wheel realization of the existing solar attitude.

The design envelope is explicit: constant positive definite reduced inertia
with Euclidean gain at most 1000 kg m², three orthogonal ideal wheels with
axial inertia at least 0.01 kg m², zero external torque, and initialized zero
total inertial angular momentum. This is an exact solution of that model.
Robust tracking, environmental torque, inertia changes and electrical power
are separate obligations. No vendor hardware is certified by these bounds.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.SolarReactionWheels
open GNC GNC.ReactionWheels GNC.RotationKinematics ChaserReferenceData Set Matrix
open scoped Matrix Matrix.Norms.Operator

structure Design where
  inertia : InertiaMatrix
  positive : inertia.PosDef
  bound : ∀ v, GNC.enorm (inertia *ᵥ v) ≤ 1000*GNC.enorm v
  spinInertia : Fin 3 → ℝ
  spin_lower : ∀ i, (1:ℝ)/100 ≤ spinInertia i

/-- An algebraic witness that the stated design envelope is nonempty.
It is not a mass/geometry or vendor hardware model. -/
def exampleDesign : Design where
  inertia := (1000:ℝ) • (1:InertiaMatrix)
  positive := Matrix.PosDef.one.smul (by norm_num : (0:ℝ)<1000)
  bound v := by simp [Matrix.smul_mulVec, GNC.enorm_smul]
  spinInertia _ := 1/100
  spin_lower _ := le_rfl

def wheelMomentum (d : Design) (r : Flow) (s : ℝ) : Vec3 :=
  momentum d.inertia ((SolarAttitudeRealization.physicalPath r).rotation s)
    ((SolarAttitudeRealization.physicalPath r).velocity s) 0

def wheelMotor (d : Design) (r : Flow) (s : ℝ) : Vec3 :=
  motor d.inertia ((SolarAttitudeRealization.physicalPath r).rotation s)
    ((SolarAttitudeRealization.physicalPath r).velocity s)
    ((SolarAttitudeRealization.physicalPath r).acceleration s) 0 0

def wheelSpeed (d : Design) (r : Flow) (s : ℝ) : Vec3 :=
  relativeSpeed d.spinInertia ((SolarAttitudeRealization.physicalPath r).velocity s)
    (wheelMomentum d r s)

def wheelAcceleration (d : Design) (r : Flow) (s : ℝ) : Vec3 :=
  relativeAcceleration d.spinInertia ((SolarAttitudeRealization.physicalPath r).acceleration s)
    (wheelMotor d r s)

theorem momentum_derivative (d : Design) (r : Flow) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5)) :
    HasDerivAt (wheelMomentum d r) (wheelMotor d r s) s :=
  ReactionWheels.momentum_derivative d.inertia
    (SolarAttitudeRealization.physical_jet r hs).1
    (SolarAttitudeRealization.physical_jet r hs).2 (hasDerivAt_const s (0:Vec3))

theorem speed_derivative (d : Design) (r : Flow) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5)) :
    HasDerivAt (wheelSpeed d r) (wheelAcceleration d r s) s :=
  relativeSpeed_derivative d.spinInertia (SolarAttitudeRealization.physical_jet r hs).2
    (momentum_derivative d r hs)

theorem euler (d : Design) (r : Flow) (s : ℝ) :
    Euler d.inertia ((SolarAttitudeRealization.physicalPath r).velocity s)
      ((SolarAttitudeRealization.physicalPath r).acceleration s)
      (wheelMomentum d r s) (wheelMotor d r s) 0 := by
  simpa only [rotate_zero] using realizes d.inertia
    ((SolarAttitudeRealization.physicalPath r).rotation s)
    ((SolarAttitudeRealization.physicalPath r).velocity s)
    ((SolarAttitudeRealization.physicalPath r).acceleration s) 0 0

theorem total_momentum_zero (d : Design) (r : Flow) (s : ℝ) :
    inertialMomentum d.inertia ((SolarAttitudeRealization.physicalPath r).rotation s)
      ((SolarAttitudeRealization.physicalPath r).velocity s) (wheelMomentum d r s) = 0 :=
  inertial_identity _ _ _ _

theorem rotor_consistency (d : Design) (r : Flow) (s : ℝ) (i : Fin 3) :
    d.spinInertia i*((SolarAttitudeRealization.physicalPath r).velocity s i+
      wheelSpeed d r s i) = wheelMomentum d r s i ∧
    d.spinInertia i*((SolarAttitudeRealization.physicalPath r).acceleration s i+
      wheelAcceleration d r s i) = wheelMotor d r s i := by
  have hj : ∀ i, d.spinInertia i ≠ 0 := fun i =>
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) (d.spin_lower i))
  exact ⟨spin_identity _ hj _ _ i, motor_identity _ hj _ _ i⟩

theorem bounds (d : Design) (r : Flow) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5)) :
    GNC.enorm (wheelMomentum d r s) ≤ 17/10 ∧
      GNC.enorm (wheelMotor d r s) ≤ 2/625 ∧
      (∀ i, |wheelSpeed d r s i| ≤ 1700017/10000) := by
  have hp := SolarAttitudeRealization.physical_bounds r hs
  have h0 : GNC.enorm (0:Vec3) ≤ 0 := (enorm_eq_zero_iff _).mpr rfl |>.le
  have hh := momentum_bound d.inertia ((SolarAttitudeRealization.physicalPath r).rotation s)
    _ (0:Vec3) d.bound hp.1 h0 (by norm_num)
  have hu := motor_bound d.inertia ((SolarAttitudeRealization.physicalPath r).rotation s)
    _ _ (0:Vec3) (0:Vec3) d.bound hp.1 hp.2 h0 h0 (by norm_num)
  norm_num at hh hu
  refine ⟨hh,hu,?_⟩
  intro i
  have hv := relativeSpeed_bound d.spinInertia _ _ (by norm_num : (0:ℝ)<1/100)
    d.spin_lower hp.1 hh i
  norm_num at hv
  exact hv

theorem continuous (d : Design) (r : Flow) :
    Continuous (wheelMomentum d r) ∧ Continuous (wheelMotor d r) ∧ Continuous (wheelSpeed d r) := by
  have hp := SolarAttitudeRealization.physical_continuous r
  have hh : Continuous (wheelMomentum d r) := by
    have hj : Continuous (fun s => d.inertia *ᵥ (SolarAttitudeRealization.physicalPath r).velocity s) :=
      continuous_const.matrix_mulVec hp.2.1
    convert hj.neg using 1
    funext s
    exact ReactionWheels.momentum_zero _ _ _
  have hu : Continuous (wheelMotor d r) := by
    have hj : Continuous (fun s => d.inertia *ᵥ (SolarAttitudeRealization.physicalPath r).acceleration s) :=
      continuous_const.matrix_mulVec hp.2.2
    convert hj.neg using 1
    funext s
    exact ReactionWheels.motor_zero _ _ _ _
  refine ⟨hh,hu,?_⟩
  apply continuous_pi
  intro i
  exact ((continuous_apply i |>.comp hh).div_const _).sub (continuous_apply i |>.comp hp.2.1)

structure Contract (d : Design) (r : Flow) : Prop where
  continuous : Continuous (wheelMomentum d r) ∧ Continuous (wheelMotor d r) ∧
    Continuous (wheelSpeed d r)
  momentum_derivative : ∀ s, s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5) →
    HasDerivAt (wheelMomentum d r) (wheelMotor d r s) s
  speed_derivative : ∀ s, s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5) →
    HasDerivAt (wheelSpeed d r) (wheelAcceleration d r s) s
  euler : ∀ s, Euler d.inertia ((SolarAttitudeRealization.physicalPath r).velocity s)
    ((SolarAttitudeRealization.physicalPath r).acceleration s)
    (wheelMomentum d r s) (wheelMotor d r s) 0
  total_momentum_zero : ∀ s,
    inertialMomentum d.inertia ((SolarAttitudeRealization.physicalPath r).rotation s)
      ((SolarAttitudeRealization.physicalPath r).velocity s) (wheelMomentum d r s) = 0
  rotor_consistency : ∀ s i,
    d.spinInertia i*((SolarAttitudeRealization.physicalPath r).velocity s i+
      wheelSpeed d r s i) = wheelMomentum d r s i ∧
    d.spinInertia i*((SolarAttitudeRealization.physicalPath r).acceleration s i+
      wheelAcceleration d r s i) = wheelMotor d r s i
  bounds : ∀ s, s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5) →
    GNC.enorm (wheelMomentum d r s) ≤ 17/10 ∧ GNC.enorm (wheelMotor d r s) ≤ 2/625 ∧
      (∀ i, |wheelSpeed d r s i| ≤ 1700017/10000)

theorem contract (d : Design) (r : Flow) : Contract d r :=
  ⟨continuous d r, fun _ => momentum_derivative d r, fun _ => speed_derivative d r,
    euler d r, total_momentum_zero d r, rotor_consistency d r, fun _ => bounds d r⟩

/-- The same reference and both terminal/propulsion-certified plans admit
the bounded ideal-wheel realization for every design in the stated envelope. -/
theorem exists_wheel_comparison (d : Design) : ∃ r : Flow,
    ReferenceFlowExistence.CertifiedProgram r ∧ SolarAttitudeRealization.Contract r ∧ Contract d r ∧
    (∀ q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa,
      ∃ m : ChaserExistence.Motion r (RetainedPhysical.commands q),
        ExistingSolarCertificate.TerminalBox r (RetainedPhysical.commands q) m ∧
        SolarPropulsion.Contract r SharedBiasCertificates.Solar.x (fun _ => q) m) ∧
    (∀ q : Fin 18 → Vec3,
      (∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) →
      ∃ m : ChaserExistence.Motion r (ComparatorPrefix.commands q),
        ExistingSolarCertificate.TerminalBox r (ComparatorPrefix.commands q) m ∧
        SolarPropulsion.Contract r SolarComparator.plan q m) := by
  obtain ⟨r,hprogram,hattitude,hcandidate,hcomparison⟩ :=
    SolarAttitudeRealization.exists_kinematic_comparison
  exact ⟨r,hprogram,hattitude,contract d r,hcandidate,hcomparison⟩

end GNC.Applications.OrbitalFuel.SolarReactionWheels
