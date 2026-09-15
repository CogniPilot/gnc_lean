import GNC.Applications.OrbitalFuel.ValidatedBurnSensitivity
import GNC.Applications.OrbitalFuel.SolarSensitivityFuel
import GNC.Applications.OrbitalFuel.SolarPropellantCertificate

/-! Solar reference-dependent finite-burn fuel certificate with proved
coefficient and free-response correspondence. The terminal RHS retains the
declared symmetric nonlinear reserve; this module does not establish that
reserve for all nonlinear trajectories or realize the commanded attitudes.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.ValidatedSolarFuel
open GNC GNC.SharedBias GNC.FuelCertificate GNC.PolynomialOrbitTransition
open SharedBiasExample (axis)
open SharedBiasCertificates.Solar

set_option maxRecDepth 100000 in
theorem sharp_allowance_bound : ∀ i j, BurnSensitivity.vectorAllowance i j ≤ (3079/10^14:ℚ) := by
  decide +kernel

theorem allowance_bound : ∀ i j, BurnSensitivity.vectorAllowance i j ≤ (1/10^10:ℚ) := by
  intro i j
  exact (sharp_allowance_bound i j).trans (by norm_num)

def physicalFree (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 6) : ℝ :=
  FreeResponse.physicalOutput (z (3/5)) (F (3/5)) (H (3/5))
    SolarSensitivityFuel.speed (Real.sqrt (3/2)) (FreeResponse.pullbackIntegrals z F) i /
      (FreeResponse.tolerance i:ℝ)

def physicalB (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 12) : ℝ :=
  let r : Fin 6 := ⟨i.val/2,by omega⟩
  FreeResponse.beta r+(if i.val%2 = 0 then 1 else -1)*physicalFree z F H r

section Flow
variable (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt z (GNC.PolynomialOrbit.rate PolynomialTransition.alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1)
include hz hF hH hdz hdF hdH hiz hiF hiH

theorem coefficient_error (i : Fin 12) (j : Fin 18) :
    GNC.enorm (BurnSensitivity.physicalH z F H i j-h i j) ≤ SolarSensitivityFuel.dataError := by
  have he := BurnSensitivity.vector_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH i j
  have hb := (Rat.cast_le (K := ℝ)).mpr (allowance_bound i j)
  norm_num [SolarSensitivityFuel.dataError] at hb ⊢
  exact he.trans hb

theorem rhs_error (i : Fin 12) : |physicalB z F H i-b i| ≤ SolarSensitivityFuel.dataError := by
  have he (r : Fin 6) := FreeResponse.rhs_enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH r
  dsimp only [FreeResponse.terminalInput] at he
  simp only [FreeResponse.constraintOutput_correct] at he
  let r : Fin 6 := ⟨i.val/2,by omega⟩
  by_cases hi : i.val%2 = 0
  · have hr : FreeResponse.negativeRow r = i := by
      ext
      dsimp [FreeResponse.negativeRow, r]
      omega
    have h := (he r).1
    rw [hr] at h
    simpa [physicalB, physicalFree, r, hi, SolarSensitivityFuel.speed,
      SolarSensitivityFuel.dataError] using h
  · have hr : FreeResponse.positiveRow r = i := by
      ext
      dsimp [FreeResponse.positiveRow, r]
      omega
    have h := (he r).2
    rw [hr] at h
    simpa [physicalB, physicalFree, r, hi, SolarSensitivityFuel.speed,
      SolarSensitivityFuel.dataError] using h

theorem candidate_feasible : CommonFeasible axis kappa (BurnSensitivity.physicalH z F H)
    (physicalB z F H) x :=
  SolarSensitivityFuel.candidate_feasible _ _
    (coefficient_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)
    (rhs_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)

theorem cost_gap (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa (BurnSensitivity.physicalH z F H) (physicalB z F H) y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) : Cost c x+15227/100000 < Cost c y :=
  SolarSensitivityFuel.cost_gap _ _
    (coefficient_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)
    (rhs_error z F H hz hF hH hdz hdF hdH hiz hiF hiH) y hy hbox

theorem physical_propellant_saving (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa (BurnSensitivity.physicalH z F H) (physicalB z F H) y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) {mass exhaust : ℝ}
    (hm : 0 < mass) (hexhaust : 0 < exhaust) :
    Propellant.consumedMass mass exhaust (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) x) <
      Propellant.consumedMass mass exhaust (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) :=
  SolarSensitivityFuel.physical_propellant_saving _ _
    (coefficient_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)
    (rhs_error z F H hz hF hH hdz hdF hdH hiz hiF hiH) y hy hbox hm hexhaust

theorem relative_delta_v_saving (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa (BurnSensitivity.physicalH z F H) (physicalB z F H) y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) x <
      (9891/10000:ℝ)*Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y := by
  have hg := SolarSensitivityFuel.relative_cost_saving _ _
    (coefficient_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)
    (rhs_error z F H hz hF hH hdz hdF hdH hiz hiF hiH) y hy hbox
  have h := mul_lt_mul_of_pos_left hg SolarSensitivityFuel.costScale_pos
  rw [SolarPropellantCertificate.cost_identity, SolarPropellantCertificate.cost_identity]
  nlinarith

theorem one_percent_propellant_saving (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa (BurnSensitivity.physicalH z F H) (physicalB z F H) y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) {mass exhaust : ℝ}
    (hm : 0 < mass) (hexhaust : 20000 ≤ exhaust) :
    Propellant.consumedMass mass exhaust (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) x) <
      (99/100:ℝ)*Propellant.consumedMass mass exhaust
        (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) :=
  SolarPropellantCertificate.one_percent_propellant _ _
    (coefficient_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)
    (rhs_error z F H hz hF hH hdz hdF hdH hiz hiF hiH) y hy hbox hm hexhaust

end Flow

/-- Specialization to the original inverse-square-gravity reference with
continuous tangential thrust. Existence and noncollision are explicit, as
in the reference/transition certificates. -/
theorem physical_reference_certificate (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hw : Continuous w) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < GNC.PolynomialOrbit.radius (w t))
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt w (GNC.PolynomialOrbit.physicalRate PolynomialTransition.alpha (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt F (planeGenerator (GNC.PolynomialOrbit.lift (w t))*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt H (normalGenerator (GNC.PolynomialOrbit.lift (w t))*H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1) :
    let z := fun t => GNC.PolynomialOrbit.lift (w t)
    CommonFeasible axis kappa (BurnSensitivity.physicalH z F H) (physicalB z F H) x ∧
    ∀ y : Fin 18 → ℝ,
      IndependentFeasible axis kappa (BurnSensitivity.physicalH z F H) (physicalB z F H) y →
      (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) x <
        (9891/10000:ℝ)*Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) ∧
      Propellant.consumedMass 500 (588399/20) (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) x) <
        (99/100:ℝ)*Propellant.consumedMass 500 (588399/20)
          (Cost (fun _ => SolarSensitivityFuel.maximumBurnCost) y) := by
  let z := fun t => GNC.PolynomialOrbit.lift (w t)
  have hz : Continuous z := GNC.PolynomialOrbit.lift_continuous hw hr
  have hdz := fun t ht => GNC.PolynomialOrbit.lift_derivative (hdw t ht) (hr t)
  have hiz : z 0 = ValidatedReference.initial := by
    change GNC.PolynomialOrbit.lift (w 0) = ValidatedReference.initial
    rw [hiw]
    norm_num [GNC.PolynomialOrbit.lift, GNC.PolynomialOrbit.radius, ValidatedReference.initial]
    exact ⟨rfl,rfl⟩
  refine ⟨candidate_feasible z F H hz hF hH hdz hdF hdH hiz hiF hiH, ?_⟩
  intro y hy hbox
  exact ⟨relative_delta_v_saving z F H hz hF hH hdz hdF hdH hiz hiF hiH y hy hbox,
    one_percent_propellant_saving z F H hz hF hH hdz hdF hdH hiz hiF hiH y hy hbox
      (by norm_num) (by norm_num)⟩

end GNC.Applications.OrbitalFuel.ValidatedSolarFuel
