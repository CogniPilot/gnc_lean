import GNC.Applications.OrbitalFuel.SolarSensitivityFuel
import GNC.Applications.OrbitalFuel.ValidatedTerminalData
import GNC.Control.PropellantBounds

/-! A quantitative ideal propellant guarantee for the solar terminal model.
Actual square-root units bound the candidate below 14 m/s and preserve more
than 0.152 m/s separation. The rocket equation then gives at least one percent
less propellant for exhaust speed at least 20 km/s, including this mission's
3000-second specific impulse. Attitude-control costs are not included. -/
noncomputable section
namespace GNC.Applications.OrbitalFuel.SolarPropellantCertificate
open GNC GNC.SharedBias GNC.FuelCertificate
open SharedBiasExample (axis)
open SharedBiasCertificates.Solar SolarSensitivityFuel

theorem scale_bounds : (99999/100000:ℝ) ≤ costScale ∧ costScale ≤ (100001/100000:ℝ) := by
  have he := TerminalData.speed_enclosure
  change |speed-(TerminalData.speedCenter:ℝ)| ≤ (1/10^25:ℝ) at he
  obtain ⟨hl,hu⟩ := abs_le.mp he
  unfold costScale
  rw [maximumBurnCost_formula]
  norm_num [TerminalData.speedCenter, BurnSensitivity.burnScale, FreeResponse.lengthUnit, c] at hl hu ⊢
  constructor <;> nlinarith

theorem cost_identity (u : Fin 18 → ℝ) :
    Cost (fun _ => maximumBurnCost) u = costScale*Cost c u := by
  simp only [Cost, Finset.mul_sum, ← mul_assoc, costScale_value]

theorem candidate_bounds :
    0 ≤ Cost (fun _ => maximumBurnCost) x ∧ Cost (fun _ => maximumBurnCost) x ≤ 14 := by
  rw [cost_identity, cost_value]
  constructor <;> nlinarith [scale_bounds.1, scale_bounds.2]

theorem physical_gap (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ dataError)
    (hb : ∀ i, |bb i-b i| ≤ dataError) (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa hh bb y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Cost (fun _ => maximumBurnCost) x+19/125 < Cost (fun _ => maximumBurnCost) y := by
  rw [cost_identity, cost_identity]
  have hg := mul_lt_mul_of_pos_left (cost_gap hh bb he hb y hy hbox) costScale_pos
  nlinarith [scale_bounds.1]

theorem one_percent_budget {J exhaust : ℝ} (hJ : 0 ≤ J) (hmax : J ≤ 14)
    (he : 20000 ≤ exhaust) :
    J/exhaust < (99/100:ℝ)*((J+19/125)/(exhaust+(J+19/125))) := by
  have hep : 0 < exhaust := by linarith
  have hden : 0 < exhaust+(J+19/125) := by linarith
  rw [← mul_div_assoc]
  apply (div_lt_div_iff₀ hep hden).mpr
  have hsq : J^2 ≤ 196 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hmax hep.le
  nlinarith

theorem one_percent_propellant (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ dataError)
    (hb : ∀ i, |bb i-b i| ≤ dataError) (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa hh bb y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) {mass exhaust : ℝ}
    (hm : 0 < mass) (hexhaust : 20000 ≤ exhaust) :
    Propellant.consumedMass mass exhaust (Cost (fun _ => maximumBurnCost) x) <
      (99/100:ℝ)*Propellant.consumedMass mass exhaust (Cost (fun _ => maximumBurnCost) y) := by
  apply Propellant.relative_saving_of_budget hm (by linarith) candidate_bounds.1
    (show 0 ≤ Cost (fun _ => maximumBurnCost) x+19/125 by linarith [candidate_bounds.1])
    (physical_gap hh bb he hb y hy hbox).le (by norm_num)
  exact one_percent_budget candidate_bounds.1 candidate_bounds.2 hexhaust

end GNC.Applications.OrbitalFuel.SolarPropellantCertificate
