import GNC.Applications.OrbitalFuel.SolarAttitudeSchedule
import GNC.Applications.OrbitalFuel.SolarPropulsionRealization
import GNC.Dynamics.PlanarAttitudeFrame
import Mathlib.Analysis.Real.Pi.Bounds

/-! A continuous inertial attitude with actual angular velocity and
acceleration for the solar burn schedule. The orbital-frame rate is included.
This is a kinematic realization, not a robust attitude-tracking controller.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.SolarAttitudeRealization
open GNC GNC.RotationKinematics GNC.PolynomialOrbit GNC.PolynomialOrbitTransition
open SolarAttitudeSchedule ChaserReferenceData Set Matrix
open scoped Matrix Matrix.Norms.Operator

def reference (r : Flow) : Path where
  rotation t := PlanarAttitudeFrame.rotation (r.w t) (r.hr t)
  velocity t := ![0,0,PlanarAttitudeFrame.spin (lift (r.w t))]
  acceleration t := ![0,0,PlanarAttitudeFrame.spinAcceleration (PolynomialTransition.alpha:ℝ)
    (lift (r.w t))]

def firstZ : Path := Path.z (angle 0) (angleRate 0) (angleAcceleration 0)
def middleX : Path := Path.x (angle 1) (angleRate 1) (angleAcceleration 1)
def lastZ : Path := Path.z (angle 2) (angleRate 2) (angleAcceleration 2)
def path (r : Flow) : Path := ((reference r).compose firstZ |>.compose middleX).compose lastZ

theorem reference_jet (r : Flow) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) :
    (reference r).HasJet t := by
  refine ⟨PlanarAttitudeFrame.physical_derivative r.hr (r.hdw t ht), ?_⟩
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const t (0:ℝ)
  · exact hasDerivAt_const t (0:ℝ)
  · exact PlanarAttitudeFrame.physical_spin_derivative (r.hr t) (r.hdw t ht)

theorem path_jet (r : Flow) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) : (path r).HasJet t :=
  Path.compose_jet _ _ (Path.compose_jet _ _ (Path.compose_jet _ _ (reference_jet r ht)
    (Path.z_jet (angle_derivative 0 t) (angleRate_derivative 0 t)))
    (Path.x_jet (angle_derivative 1 t) (angleRate_derivative 1 t)))
    (Path.z_jet (angle_derivative 2 t) (angleRate_derivative 2 t))

theorem reference_continuous (r : Flow) : (reference r).HasContinuousJet := by
  have hz := lift_continuous r.hw r.hr
  refine ⟨frame_continuous _ hz, ?_, ?_⟩
  · apply continuous_pi
    intro i
    fin_cases i <;> simp [reference, PlanarAttitudeFrame.spin] <;> fun_prop
  · apply continuous_pi
    intro i
    fin_cases i <;> simp [reference, PlanarAttitudeFrame.spinAcceleration] <;> fun_prop

theorem path_continuous (r : Flow) : (path r).HasContinuousJet :=
  Path.compose_continuous _ _ (Path.compose_continuous _ _
    (Path.compose_continuous _ _ (reference_continuous r)
      (Path.z_continuous (angle_derivative 0) (angleRate_derivative 0) (angleAcceleration_continuous 0)))
    (Path.x_continuous (angle_derivative 1) (angleRate_derivative 1) (angleAcceleration_continuous 1)))
    (Path.z_continuous (angle_derivative 2) (angleRate_derivative 2) (angleAcceleration_continuous 2))

theorem on_burn (r : Flow) (j : Fin 18) {t : ℝ}
    (ht : t ∈ Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    (path r).rotation t = PlanarAttitudeFrame.rotation (r.w t) (r.hr t)*
      SharedBiasGeometry.cycleRotation j := by
  have h := rotation_on_burn j ht
  change _*_*_*_ = _*_
  rw [← h, SolarAttitudeSchedule.rotation]
  simp [path, Path.compose, reference, firstZ, middleX, lastZ, Path.x, Path.z, mul_assoc]

theorem lift_bound (r : Flow) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) :
    ∀ i, |lift (r.w t) i| ≤ 4/3 := by
  have h := Reference.physical_solar_annulus r.w r.hw r.hdw r.hiw t ht
  have hp0 := component_le_enorm (position (r.w t)) 0
  have hp1 := component_le_enorm (position (r.w t)) 1
  have hv0 := component_le_enorm (PolynomialOrbitTransition.velocity (r.w t)) 0
  have hv1 := component_le_enorm (PolynomialOrbitTransition.velocity (r.w t)) 1
  rw [position_norm] at hp0 hp1
  intro i
  fin_cases i
  · simpa only [lift, Matrix.cons_val_zero] using (hp0.trans (by linarith : radius (r.w t) ≤ 4/3))
  · simpa only [lift, Matrix.cons_val_one] using (hp1.trans (by linarith : radius (r.w t) ≤ 4/3))
  · simpa only [lift, position, PolynomialOrbitTransition.velocity, Matrix.cons_val_zero,
      Matrix.cons_val_two] using (hv0.trans (by linarith : GNC.enorm (PolynomialOrbitTransition.velocity (r.w t)) ≤ 4/3))
  · simpa only [lift, PolynomialOrbitTransition.velocity, Matrix.cons_val_one,
      Matrix.cons_val_three] using (hv1.trans (by linarith : GNC.enorm (PolynomialOrbitTransition.velocity (r.w t)) ≤ 4/3))
  · change |(radius (r.w t))⁻¹| ≤ 4/3
    rw [abs_of_pos (inv_pos.mpr (r.hr t)), inv_eq_one_div, div_le_iff₀ (r.hr t)]
    linarith [h.1]

theorem reference_bounds (r : Flow) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) :
    GNC.enorm ((reference r).velocity t) ≤ 7 ∧ GNC.enorm ((reference r).acceleration t) ≤ 82 := by
  simpa only [reference, z_axis_norm] using PlanarAttitudeFrame.spin_bounds (lift_bound r ht)
    (show |(PolynomialTransition.alpha:ℝ)| ≤ 1 by norm_num [PolynomialTransition.alpha])

theorem normalized_bounds (r : Flow) {t : ℝ} (ht : t ∈ Icc (0:ℝ) (3/5)) :
    GNC.enorm ((path r).velocity t) ≤ 8500 ∧
      GNC.enorm ((path r).acceleration t) ≤ 80000000 := by
  have hr := reference_bounds r ht
  have hy : GNC.enorm (firstZ.velocity t) = |angleRate 0 t| := z_axis_norm _
  have hp : GNC.enorm (middleX.velocity t) = |angleRate 1 t| := x_axis_norm _
  have hl : GNC.enorm (lastZ.velocity t) = |angleRate 2 t| := z_axis_norm _
  have hya : GNC.enorm (firstZ.acceleration t) = |angleAcceleration 0 t| := z_axis_norm _
  have hpa : GNC.enorm (middleX.acceleration t) = |angleAcceleration 1 t| := x_axis_norm _
  have hla : GNC.enorm (lastZ.acceleration t) = |angleAcceleration 2 t| := z_axis_norm _
  have h1 := Path.compose_bounds (reference r) firstZ t hr.1 hy.le hr.2 hya.le
  have h2 := Path.compose_bounds ((reference r).compose firstZ) middleX t h1.1 hp.le h1.2 hpa.le
  have h3 := Path.compose_bounds (((reference r).compose firstZ).compose middleX) lastZ t
    h2.1 hl.le h2.2 hla.le
  have hs := coordinate_sum_bounds t
  have hv : 7+|angleRate 0 t|+|angleRate 1 t|+|angleRate 2 t| ≤ 8500 := by
    linarith [Real.pi_lt_d2]
  have ha : 82+|angleAcceleration 0 t|+|angleAcceleration 1 t|+|angleAcceleration 2 t| ≤ 5100000 := by
    linarith [Real.pi_lt_d2]
  dsimp only [path]
  constructor
  · exact h3.1.trans hv
  · have hsq : (7+|angleRate 0 t|+|angleRate 1 t|+|angleRate 2 t|)^2 ≤ 8500^2 :=
      pow_le_pow_left₀ (by positivity) hv 2
    have h01 := mul_nonneg (abs_nonneg (angleRate 0 t)) (abs_nonneg (angleRate 1 t))
    have h02 := mul_nonneg (abs_nonneg (angleRate 0 t)) (abs_nonneg (angleRate 2 t))
    have h12 := mul_nonneg (abs_nonneg (angleRate 1 t)) (abs_nonneg (angleRate 2 t))
    nlinarith [h3.2, sq_nonneg (angleRate 0 t), sq_nonneg (angleRate 1 t),
      sq_nonneg (angleRate 2 t), abs_nonneg (angleRate 0 t), abs_nonneg (angleRate 1 t),
      abs_nonneg (angleRate 2 t), sq_abs (angleRate 0 t), sq_abs (angleRate 1 t), sq_abs (angleRate 2 t)]

def physicalPath (r : Flow) : Path := (path r).rescale SolarPropulsion.timeScale

theorem physical_continuous (r : Flow) : (physicalPath r).HasContinuousJet :=
  Path.rescale_continuous _ (path_continuous r) _

theorem physical_rotation_continuous (r : Flow) : Continuous ((physicalPath r).rotation) :=
  continuous_induced_rng.mpr (physical_continuous r).1

theorem physical_jet (r : Flow) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5)) : (physicalPath r).HasJet s :=
  Path.rescale_jet _ _ _ (path_jet r hs)

theorem thrust_direction_on_burn (r : Flow) (j : Fin 18) (q : Vec3) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈
      Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    rotate ((physicalPath r).rotation s) q =
      polynomialFrame (lift (r.w (s/SolarPropulsion.timeScale))) *ᵥ
        rotate (SharedBiasGeometry.cycleRotation j) q := by
  change rotate ((path r).rotation (s/SolarPropulsion.timeScale)) q = _
  rw [on_burn r j hs, rotate_mul]
  rfl

theorem force_on_burn (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3) (j : Fin 18) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈
      Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75)) :
    SolarPropulsion.force r y q (2*j.val+1) s =
      SolarPropulsion.mass y s • ((y j/10000) • rotate ((physicalPath r).rotation s) (q j)) := by
  rw [SolarPropulsion.force, SolarPropulsion.accelerationSI, BurnSchedule.input_burn,
    thrust_direction_on_burn r j (q j) hs]

theorem timeScale_lower : (5000000:ℝ) ≤ SolarPropulsion.timeScale := by
  have h := SolarPropulsion.timeScale_sq
  norm_num [SolarPropulsion.length, SolarPropulsion.mu, FreeResponse.lengthUnit] at h
  nlinarith [SolarPropulsion.timeScale_pos]

/-- Conservative all-time body-rate and body-acceleration bounds in SI
seconds. The allowance uses the total variation of all coast angles. -/
theorem physical_bounds (r : Flow) {s : ℝ}
    (hs : s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5)) :
    GNC.enorm ((physicalPath r).velocity s) ≤ 17/10000 ∧
      GNC.enorm ((physicalPath r).acceleration s) ≤ 1/312500 := by
  have h := normalized_bounds r hs
  have ht := SolarPropulsion.timeScale_pos
  have ht2 : 0 < SolarPropulsion.timeScale^2 := sq_pos_of_pos ht
  simp only [physicalPath, Path.rescale, GNC.enorm_smul, abs_of_pos (one_div_pos.mpr ht),
    abs_of_pos (one_div_pos.mpr ht2), one_div_mul_eq_div]
  constructor
  · rw [div_le_iff₀ ht]
    linarith [timeScale_lower]
  · rw [div_le_iff₀ ht2]
    nlinarith [timeScale_lower]

structure Contract (r : Flow) : Prop where
  continuous : (physicalPath r).HasContinuousJet
  continuous_rotation : Continuous ((physicalPath r).rotation)
  kinematics : ∀ s, s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5) →
    (physicalPath r).HasJet s
  bounds : ∀ s, s/SolarPropulsion.timeScale ∈ Icc (0:ℝ) (3/5) →
    GNC.enorm ((physicalPath r).velocity s) ≤ 17/10000 ∧
      GNC.enorm ((physicalPath r).acceleration s) ≤ 1/312500
  force : ∀ (y : Fin 18 → ℝ) (q : Fin 18 → Vec3) (j : Fin 18) s,
    s/SolarPropulsion.timeScale ∈ Icc ((j.val:ℝ)/30+1/150) ((j.val:ℝ)/30+2/75) →
    SolarPropulsion.force r y q (2*j.val+1) s =
      SolarPropulsion.mass y s • ((y j/10000) • rotate ((physicalPath r).rotation s) (q j))

theorem contract (r : Flow) : Contract r :=
  ⟨physical_continuous r, physical_rotation_continuous r, fun _ => physical_jet r,
    fun _ => physical_bounds r, fun y q j _ => force_on_burn r y q j⟩

/-- The kinematic attitude construction belongs to the same existing
reference and both stored terminal/propulsion-certified nonlinear plans. -/
theorem exists_kinematic_comparison : ∃ r : Flow,
    ReferenceFlowExistence.CertifiedProgram r ∧ Contract r ∧
    (∀ q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa,
      ∃ m : ChaserExistence.Motion r (RetainedPhysical.commands q),
        ExistingSolarCertificate.TerminalBox r (RetainedPhysical.commands q) m ∧
        SolarPropulsion.Contract r SharedBiasCertificates.Solar.x (fun _ => q) m) ∧
    (∀ q : Fin 18 → Vec3,
      (∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) →
      ∃ m : ChaserExistence.Motion r (ComparatorPrefix.commands q),
        ExistingSolarCertificate.TerminalBox r (ComparatorPrefix.commands q) m ∧
        SolarPropulsion.Contract r SolarComparator.plan q m) := by
  obtain ⟨r,hprogram,hcandidate,hcomparison⟩ := SolarPropulsion.exists_propulsion_comparison
  exact ⟨r,hprogram,contract r,hcandidate,hcomparison⟩

end GNC.Applications.OrbitalFuel.SolarAttitudeRealization
