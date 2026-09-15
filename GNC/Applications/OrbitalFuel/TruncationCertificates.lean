import GNC.Control.FuelRobustness
import GNC.Applications.OrbitalFuel.RegionalCertificates
import GNC.Applications.OrbitalFuel.StrongBaselines

/-! Conditional certificates under bounded exact-program data errors.
The stated error allowance has not been certified for an orbital integrator. -/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open GNC.FuelCertificate
namespace GNC.Applications.OrbitalFuel.Truncation


namespace EarthBall
def x : Fin 18 → ℝ := ![0, 0, 0, (185121505733/200000000000), 0, 0, 0, (29887628979/100000000000), (20767299971/500000000000), 0, 0, 0, 0, 0, 0, 1, (60738419117/500000000000), (5048588217/62500000000)]
theorem in_box : ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  intro j
  fin_cases j <;> norm_num [x]
theorem tightened_feasible :
    Feasible (fun i j => Regional.EarthCap.A i j+(1/36000)) (fun i => Regional.EarthCap.b i-(1/2000)) x := by
  intro i
  fin_cases i <;> norm_num [Regional.EarthCap.A, Regional.EarthCap.b, x, Fin.sum_univ_succ]
theorem cost_value : Cost Regional.EarthCap.c x = (143838526814963742386427/1000000000000000000000000) := by
  norm_num [Cost, Regional.EarthCap.c, x, Fin.sum_univ_succ]
theorem error_allowance :
    lowerAllowance Regional.EarthBall.ell (fun _ _ => (1/36000)) (fun _ => (1/2000))
      (fun _ : Fin 18 => 0) = (52638229283/500000000000000) := by
  norm_num [lowerAllowance, rowAllowance, Regional.EarthBall.ell, Fin.sum_univ_succ]
theorem strict_gap : Cost Regional.EarthCap.c x < boxLower Regional.EarthBall.A Regional.EarthBall.b Regional.EarthBall.c Regional.EarthBall.ell-
    lowerAllowance Regional.EarthBall.ell (fun _ _ => (1/36000)) (fun _ => (1/2000)) (fun _ : Fin 18 => 0) := by
  rw [cost_value, Regional.EarthBall.dual_value, error_allowance]
  norm_num

/-- For every pair of exact programs within the declared coefficient/RHS
allowances, this candidate is feasible and consumes less propellant than
every feasible unit-box plan of the comparison program. -/
theorem physical_fuel_saving (Ac Ab : Fin 12 → Fin 18 → ℝ) (bc bb : Fin 12 → ℝ)
    (hAc : ∀ i j, |Ac i j-Regional.EarthCap.A i j| ≤ (1/36000))
    (hAb : ∀ i j, |Ab i j-Regional.EarthBall.A i j| ≤ (1/36000))
    (hbc : ∀ i, |bc i-Regional.EarthCap.b i| ≤ (1/2000))
    (hbb : ∀ i, |bb i-Regional.EarthBall.b i| ≤ (1/2000)) :
    Feasible Ac bc x ∧ ∀ y, Feasible Ab bb y → (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      GNC.Propellant.consumedMass 200 (196133/10) (Cost Regional.EarthCap.c x) <
      GNC.Propellant.consumedMass 200 (196133/10) (Cost Regional.EarthBall.c y) := by
  refine ⟨feasible_of_errors Ac Regional.EarthCap.A (fun _ _ => (1/36000)) bc Regional.EarthCap.b
    (fun _ => (1/2000)) x hAc hbc (fun j => (in_box j).1) tightened_feasible, ?_⟩
  intro y hy hbox
  exact strict_propellant_of_errors Ab Regional.EarthBall.A (fun _ _ => (1/36000)) bb Regional.EarthBall.b
    (fun _ => (1/2000)) Regional.EarthBall.ell Regional.EarthBall.c Regional.EarthBall.c (fun _ => 0) x y
    (by norm_num) (by norm_num) hAb hbb (fun _ => by simp) Regional.EarthBall.multiplier_nonneg hy hbox
    (le_refl _) strict_gap
end EarthBall


namespace EarthCylinder
def x : Fin 18 → ℝ := ![0, 0, 0, (925529349079/1000000000000), 0, 0, 0, (298815608687/1000000000000), (20687077807/500000000000), 0, 0, 0, 0, 0, 0, 1, (15101781173/125000000000), (4037003587/50000000000)]
theorem in_box : ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  intro j
  fin_cases j <;> norm_num [x]
theorem tightened_feasible :
    Feasible (fun i j => Regional.EarthCap.A i j+(1/3600000)) (fun i => Regional.EarthCap.b i-(1/200000)) x := by
  intro i
  fin_cases i <;> norm_num [Regional.EarthCap.A, Regional.EarthCap.b, x, Fin.sum_univ_succ]
theorem cost_value : Cost Regional.EarthCap.c x = (17972537062806685132317/125000000000000000000000) := by
  norm_num [Cost, Regional.EarthCap.c, x, Fin.sum_univ_succ]
theorem error_allowance :
    lowerAllowance StrongBaselines.EarthCylinder.ell (fun _ _ => (1/3600000)) (fun _ => (1/200000))
      (fun _ : Fin 18 => 0) = (103452498713/100000000000000000) := by
  norm_num [lowerAllowance, rowAllowance, StrongBaselines.EarthCylinder.ell, Fin.sum_univ_succ]
theorem strict_gap : Cost Regional.EarthCap.c x < boxLower StrongBaselines.EarthCylinder.A StrongBaselines.EarthCylinder.b StrongBaselines.EarthCylinder.c StrongBaselines.EarthCylinder.ell-
    lowerAllowance StrongBaselines.EarthCylinder.ell (fun _ _ => (1/3600000)) (fun _ => (1/200000)) (fun _ : Fin 18 => 0) := by
  rw [cost_value, StrongBaselines.EarthCylinder.dual_value, error_allowance]
  norm_num

/-- For every pair of exact programs within the declared coefficient/RHS
allowances, this candidate is feasible and consumes less propellant than
every feasible unit-box plan of the comparison program. -/
theorem physical_fuel_saving (Ac Ab : Fin 12 → Fin 18 → ℝ) (bc bb : Fin 12 → ℝ)
    (hAc : ∀ i j, |Ac i j-Regional.EarthCap.A i j| ≤ (1/3600000))
    (hAb : ∀ i j, |Ab i j-StrongBaselines.EarthCylinder.A i j| ≤ (1/3600000))
    (hbc : ∀ i, |bc i-Regional.EarthCap.b i| ≤ (1/200000))
    (hbb : ∀ i, |bb i-StrongBaselines.EarthCylinder.b i| ≤ (1/200000)) :
    Feasible Ac bc x ∧ ∀ y, Feasible Ab bb y → (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      GNC.Propellant.consumedMass 200 (196133/10) (Cost Regional.EarthCap.c x) <
      GNC.Propellant.consumedMass 200 (196133/10) (Cost StrongBaselines.EarthCylinder.c y) := by
  refine ⟨feasible_of_errors Ac Regional.EarthCap.A (fun _ _ => (1/3600000)) bc Regional.EarthCap.b
    (fun _ => (1/200000)) x hAc hbc (fun j => (in_box j).1) tightened_feasible, ?_⟩
  intro y hy hbox
  exact strict_propellant_of_errors Ab StrongBaselines.EarthCylinder.A (fun _ _ => (1/3600000)) bb StrongBaselines.EarthCylinder.b
    (fun _ => (1/200000)) StrongBaselines.EarthCylinder.ell StrongBaselines.EarthCylinder.c StrongBaselines.EarthCylinder.c (fun _ => 0) x y
    (by norm_num) (by norm_num) hAb hbb (fun _ => by simp) StrongBaselines.EarthCylinder.multiplier_nonneg hy hbox
    (le_refl _) strict_gap
end EarthCylinder


namespace SolarBall
def x : Fin 18 → ℝ := ![0, (404494248839/1000000000000), 0, (80191626741/250000000000), 0, (46940511371/1000000000000), 0, 0, 0, 0, 0, 0, 0, 0, (55117126979/1000000000000), (46825545007/200000000000), (320846965583/1000000000000), 0]
theorem in_box : ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  intro j
  fin_cases j <;> norm_num [x]
theorem tightened_feasible :
    Feasible (fun i j => Regional.SolarCap.A i j+(1/36000)) (fun i => Regional.SolarCap.b i-(1/2000)) x := by
  intro i
  fin_cases i <;> norm_num [Regional.SolarCap.A, Regional.SolarCap.b, x, Fin.sum_univ_succ]
theorem cost_value : Cost Regional.SolarCap.c x = (3471382268004721390993593/250000000000000000000000) := by
  norm_num [Cost, Regional.SolarCap.c, x, Fin.sum_univ_succ]
theorem error_allowance :
    lowerAllowance Regional.SolarBall.ell (fun _ _ => (1/36000)) (fun _ => (1/2000))
      (fun _ : Fin 18 => 0) = (862995988529/1000000000000000) := by
  norm_num [lowerAllowance, rowAllowance, Regional.SolarBall.ell, Fin.sum_univ_succ]
theorem strict_gap : Cost Regional.SolarCap.c x < boxLower Regional.SolarBall.A Regional.SolarBall.b Regional.SolarBall.c Regional.SolarBall.ell-
    lowerAllowance Regional.SolarBall.ell (fun _ _ => (1/36000)) (fun _ => (1/2000)) (fun _ : Fin 18 => 0) := by
  rw [cost_value, Regional.SolarBall.dual_value, error_allowance]
  norm_num

/-- For every pair of exact programs within the declared coefficient/RHS
allowances, this candidate is feasible and consumes less propellant than
every feasible unit-box plan of the comparison program. -/
theorem physical_fuel_saving (Ac Ab : Fin 12 → Fin 18 → ℝ) (bc bb : Fin 12 → ℝ)
    (hAc : ∀ i j, |Ac i j-Regional.SolarCap.A i j| ≤ (1/36000))
    (hAb : ∀ i j, |Ab i j-Regional.SolarBall.A i j| ≤ (1/36000))
    (hbc : ∀ i, |bc i-Regional.SolarCap.b i| ≤ (1/2000))
    (hbb : ∀ i, |bb i-Regional.SolarBall.b i| ≤ (1/2000)) :
    Feasible Ac bc x ∧ ∀ y, Feasible Ab bb y → (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      GNC.Propellant.consumedMass 500 (588399/20) (Cost Regional.SolarCap.c x) <
      GNC.Propellant.consumedMass 500 (588399/20) (Cost Regional.SolarBall.c y) := by
  refine ⟨feasible_of_errors Ac Regional.SolarCap.A (fun _ _ => (1/36000)) bc Regional.SolarCap.b
    (fun _ => (1/2000)) x hAc hbc (fun j => (in_box j).1) tightened_feasible, ?_⟩
  intro y hy hbox
  exact strict_propellant_of_errors Ab Regional.SolarBall.A (fun _ _ => (1/36000)) bb Regional.SolarBall.b
    (fun _ => (1/2000)) Regional.SolarBall.ell Regional.SolarBall.c Regional.SolarBall.c (fun _ => 0) x y
    (by norm_num) (by norm_num) hAb hbb (fun _ => by simp) Regional.SolarBall.multiplier_nonneg hy hbox
    (le_refl _) strict_gap
end SolarBall


namespace SolarCylinder
def x : Fin 18 → ℝ := ![0, (404488207759/1000000000000), 0, (80191630521/250000000000), 0, (23466461207/500000000000), 0, 0, 0, 0, 0, 0, 0, 0, (2755255253/50000000000), (14632332897/62500000000), (320837640907/1000000000000), 0]
theorem in_box : ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  intro j
  fin_cases j <;> norm_num [x]
theorem tightened_feasible :
    Feasible (fun i j => Regional.SolarCap.A i j+(1/3600000)) (fun i => Regional.SolarCap.b i-(1/200000)) x := by
  intro i
  fin_cases i <;> norm_num [Regional.SolarCap.A, Regional.SolarCap.b, x, Fin.sum_univ_succ]
theorem cost_value : Cost Regional.SolarCap.c x = (108477136061694922756419/7812500000000000000000) := by
  norm_num [Cost, Regional.SolarCap.c, x, Fin.sum_univ_succ]
theorem error_allowance :
    lowerAllowance StrongBaselines.SolarCylinder.ell (fun _ _ => (1/3600000)) (fun _ => (1/200000))
      (fun _ : Fin 18 => 0) = (170974327511/20000000000000000) := by
  norm_num [lowerAllowance, rowAllowance, StrongBaselines.SolarCylinder.ell, Fin.sum_univ_succ]
theorem strict_gap : Cost Regional.SolarCap.c x < boxLower StrongBaselines.SolarCylinder.A StrongBaselines.SolarCylinder.b StrongBaselines.SolarCylinder.c StrongBaselines.SolarCylinder.ell-
    lowerAllowance StrongBaselines.SolarCylinder.ell (fun _ _ => (1/3600000)) (fun _ => (1/200000)) (fun _ : Fin 18 => 0) := by
  rw [cost_value, StrongBaselines.SolarCylinder.dual_value, error_allowance]
  norm_num

/-- For every pair of exact programs within the declared coefficient/RHS
allowances, this candidate is feasible and consumes less propellant than
every feasible unit-box plan of the comparison program. -/
theorem physical_fuel_saving (Ac Ab : Fin 12 → Fin 18 → ℝ) (bc bb : Fin 12 → ℝ)
    (hAc : ∀ i j, |Ac i j-Regional.SolarCap.A i j| ≤ (1/3600000))
    (hAb : ∀ i j, |Ab i j-StrongBaselines.SolarCylinder.A i j| ≤ (1/3600000))
    (hbc : ∀ i, |bc i-Regional.SolarCap.b i| ≤ (1/200000))
    (hbb : ∀ i, |bb i-StrongBaselines.SolarCylinder.b i| ≤ (1/200000)) :
    Feasible Ac bc x ∧ ∀ y, Feasible Ab bb y → (∀ j, 0 ≤ y j ∧ y j ≤ 1) →
      GNC.Propellant.consumedMass 500 (588399/20) (Cost Regional.SolarCap.c x) <
      GNC.Propellant.consumedMass 500 (588399/20) (Cost StrongBaselines.SolarCylinder.c y) := by
  refine ⟨feasible_of_errors Ac Regional.SolarCap.A (fun _ _ => (1/3600000)) bc Regional.SolarCap.b
    (fun _ => (1/200000)) x hAc hbc (fun j => (in_box j).1) tightened_feasible, ?_⟩
  intro y hy hbox
  exact strict_propellant_of_errors Ab StrongBaselines.SolarCylinder.A (fun _ _ => (1/3600000)) bb StrongBaselines.SolarCylinder.b
    (fun _ => (1/200000)) StrongBaselines.SolarCylinder.ell StrongBaselines.SolarCylinder.c StrongBaselines.SolarCylinder.c (fun _ => 0) x y
    (by norm_num) (by norm_num) hAb hbb (fun _ => by simp) StrongBaselines.SolarCylinder.multiplier_nonneg hy hbox
    (le_refl _) strict_gap
end SolarCylinder

end GNC.Applications.OrbitalFuel.Truncation
