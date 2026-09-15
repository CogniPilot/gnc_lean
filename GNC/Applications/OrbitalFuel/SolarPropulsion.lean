import GNC.Applications.OrbitalFuel.CertifiedSolarComparison
import GNC.Control.PulsePropellant
import GNC.Dynamics.PhysicalScaling

/-! Exact SI mass and ideal-throttle realization of the solar burn program.
The mass stays positive, the vector thrust is at most 50 mN, and the actual
mass-flow equation agrees with the fuel objective. Thrust switching is ideal;
attitude tracking, throttle slew and propulsion hardware errors are not assumed
to follow from this magnitude certificate.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.SolarPropulsion
open GNC PolynomialOrbit PolynomialOrbitTransition PolynomialBurn Set Matrix
open ChaserReferenceData ChaserExistence

def length : ℝ := (FreeResponse.lengthUnit:ℝ)
def mu : ℝ := 132712440018000000000
def timeScale : ℝ := SolarSensitivityFuel.timeUnit
def exhaust : ℝ := 588399/20
def accelerationScale : ℝ := length/timeScale^2
def amplitude (y : Fin 18 → ℝ) (k : ℕ) : ℝ := BurnSchedule.input (fun j _ => y j/10000) k 0
def mass (y : Fin 18 → ℝ) (s : ℝ) : ℝ :=
  PulsePropellant.mass nodes (amplitude y) 37 timeScale 500 exhaust s
def accelerationSI (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3) (k : ℕ) (s : ℝ) : Vec3 :=
  BurnSchedule.input (fun j t => (y j/10000) •
    (polynomialFrame (lift (r.w (t/timeScale))) *ᵥ rotate (SharedBiasGeometry.cycleRotation j) (q j))) k s
def force (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3) (k : ℕ) (s : ℝ) : Vec3 :=
  mass y s • accelerationSI r y q k s

theorem length_pos : 0 < length := by norm_num [length,FreeResponse.lengthUnit]
theorem timeScale_pos : 0 < timeScale := by
  unfold timeScale SolarSensitivityFuel.timeUnit
  apply Real.sqrt_pos.mpr
  norm_num [FreeResponse.lengthUnit]
theorem timeScale_sq : timeScale^2 = length^3/mu := by
  exact Real.sq_sqrt (by norm_num [length,mu,FreeResponse.lengthUnit])
theorem scaling : mu/length^2 = accelerationScale := by
  unfold accelerationScale
  rw [timeScale_sq]
  field_simp [length_pos.ne']
theorem burn_scaling : accelerationScale*(RetainedPrefix.beta:ℝ) = 1/10000 := by
  rw [← scaling]
  norm_num [mu,length,FreeResponse.lengthUnit,RetainedPrefix.beta,BurnSensitivity.burnScale]

theorem amplitude_bounds (y : Fin 18 → ℝ) (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (k : ℕ) :
    0 ≤ amplitude y k ∧ amplitude y k ≤ 1/10000 := by
  unfold amplitude BurnSchedule.input
  split_ifs
  · constructor
    · exact div_nonneg (hy _).1 (by norm_num)
    · exact div_le_div_of_nonneg_right (hy _).2 (by norm_num)
  · norm_num

theorem mass_bounds (y : Fin 18 → ℝ) (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (s : ℝ) :
    0 < mass y s ∧ mass y s ≤ 500 :=
  PulsePropellant.mass_bounds nodes (amplitude y) 37 timeScale 500 exhaust s nodes_monotone
    (fun k _ => (amplitude_bounds y hy k).1) timeScale_pos.le (by norm_num) (by norm_num [exhaust])

theorem acceleration_norm (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (k : ℕ) (s : ℝ) : GNC.enorm (accelerationSI r y q k s) = amplitude y k := by
  unfold accelerationSI amplitude BurnSchedule.input
  split_ifs
  · rw [GNC.enorm_smul,abs_of_nonneg (div_nonneg (hy _).1 (by norm_num)),
      frame_enorm _ (r.hr _),GNC.rotate_enorm,ThrustSupport.unit_enorm _ (hq _).1,mul_one]
  · simp [GNC.enorm]

theorem acceleration_matches (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (k : ℕ) (s : ℝ) :
    accelerationSI r y q k s = accelerationScale •
      acceleration r (IndependentTerminalSafety.commands y q) k (s/timeScale) := by
  unfold accelerationSI acceleration BurnSchedule.input
  split_ifs
  · simp only [IndependentTerminalSafety.commands,ChaserResponse.acceleration,Matrix.mulVec_smul,smul_smul]
    rw [← mul_assoc,burn_scaling]
    congr 1
    ring
  · simp

theorem force_norm (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (k : ℕ) (s : ℝ) : GNC.enorm (force r y q k s) = mass y s*amplitude y k := by
  rw [force,GNC.enorm_smul,abs_of_pos (mass_bounds y hy s).1,acceleration_norm r y q hy hq]

theorem force_limit (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (k : ℕ) (s : ℝ) : GNC.enorm (force r y q k s) ≤ 1/20 := by
  rw [force_norm r y q hy hq]
  have h := mul_le_mul (mass_bounds y hy s).2 (amplitude_bounds y hy k).2
    (amplitude_bounds y hy k).1 (by norm_num : (0:ℝ) ≤ 500)
  norm_num at h ⊢
  exact h

theorem mass_flow (r : Flow) (y : Fin 18 → ℝ) (q : Fin 18 → Vec3)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (hq : ∀ j, q j ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa)
    (k : ℕ) (hk : k < 37) (s : ℝ)
    (hs : s/timeScale ∈ Ioo (nodes k) (nodes (k+1))) :
    HasDerivAt (mass y) (-GNC.enorm (force r y q k s)/exhaust) s := by
  rw [force_norm r y q hy hq]
  exact PulsePropellant.mass_flow nodes (amplitude y) nodes_monotone hk timeScale_pos hs

theorem terminal_impulse (y : Fin 18 → ℝ) :
    PulsePropellant.impulse nodes (amplitude y) 37 timeScale (timeScale*(3/5)) =
      FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y := by
  have h := ComparatorPrefix.arc_budget_general (fun j => y j/10000) (3/5)
  change ArcGronwall.prefixBudget nodes (amplitude y) 37 (3/5) = _ at h
  have he (j : Fin 18) :
      min (3/5:ℝ) (burnFinish j:ℝ)-min (3/5:ℝ) (burnStart j:ℝ) = 1/50 := by
    have hj := burn_range j
    have hb : (burnFinish j:ℝ) ≤ (3/5:ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hj.2.2
      norm_num at h ⊢
      exact h
    have ha : (burnStart j:ℝ) ≤ (3/5:ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (hj.2.1.trans hj.2.2)
      norm_num at h ⊢
      exact h
    rw [min_eq_right hb,min_eq_right ha]
    have h := congrArg (fun a : ℚ => (a:ℝ)) (burn_duration j)
    norm_num at h ⊢
    exact h
  simp_rw [he] at h
  unfold PulsePropellant.impulse
  rw [mul_div_cancel_left₀ _ timeScale_pos.ne',h,Finset.mul_sum]
  unfold FuelCertificate.Cost
  apply Finset.sum_congr rfl
  intro j _
  dsimp [SolarSensitivityFuel.maximumBurnCost,timeScale]
  ring

theorem terminal_consumption (y : Fin 18 → ℝ) :
    500-mass y (timeScale*(3/5)) = Propellant.consumedMass 500 exhaust
      (FuelCertificate.Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) := by
  unfold mass PulsePropellant.mass Propellant.consumedMass
  rw [terminal_impulse]

end GNC.Applications.OrbitalFuel.SolarPropulsion
