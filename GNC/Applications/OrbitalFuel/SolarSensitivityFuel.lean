import GNC.Applications.OrbitalFuel.SharedBiasGeometry
import GNC.Applications.OrbitalFuel.TerminalData
import GNC.Applications.OrbitalFuel.BurnSensitivityFormula
import GNC.Control.SharedBiasRobustness

/-! The stored solar candidate and every feasible independent-bias comparator
retain their strict cost separation after both vector and RHS errors of
10^-10. The exact SI maximum-burn cost is a common positive scaling of the
stored rational cost, so no rounded square root is treated as exact. -/
noncomputable section
open Matrix Finset
namespace GNC.Applications.OrbitalFuel.SolarSensitivityFuel
open GNC GNC.SharedBias GNC.FuelCertificate
open SharedBiasExample (axis)
open SharedBiasCertificates.Solar

def dataError : ℝ := 1/10^10

theorem candidate_charge : dataError+∑ j, x j*dataError < (3/10^10:ℝ) := by
  norm_num [dataError, x, Fin.sum_univ_succ]

theorem candidate_budget (i : Fin 12) :
    s i-ell i*kappa+dataError+∑ j, x j*dataError ≤ b i := by
  fin_cases i <;> norm_num [s, ell, kappa, b, x, dataError, Fin.sum_univ_succ]

theorem lower_charge :
    lowerAllowance dual (fun (_ : Fin 12) (_ : Fin 18) => dataError)
      (fun _ => dataError) (fun _ => 0) < (1/10^6:ℝ) := by
  norm_num [lowerAllowance, rowAllowance, dual, dataError, Fin.sum_univ_succ]

theorem candidate_feasible (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ dataError)
    (hb : ∀ i, |bb i-b i| ≤ dataError) : CommonFeasible axis kappa hh bb x := by
  apply common_feasible_of_errors axis kappa hh h (fun _ _ => dataError)
    bb b (fun _ => dataError) x he hb (fun j => (in_box j).1)
  apply common_of_certificate axis kappa h _ x ell s
    support_certificate.1 support_certificate.2.1
  · intro i
    rw [combined_value]
    exact support_certificate.2.2.1 i
  · intro i
    linarith [candidate_budget i]

theorem cost_gap (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ dataError)
    (hb : ∀ i, |bb i-b i| ≤ dataError) (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa hh bb y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Cost c x+15227/100000 < Cost c y := by
  have hl := independent_lower_of_errors axis kappa hh h (fun _ _ => dataError)
    bb b (fun _ => dataError) dual c c (fun _ => 0) y q he hb (by intro j; simp)
    witnesses dual_nonneg hy hbox
  change boxLower A b c dual-_ ≤ Cost c y at hl
  linarith [SharedBiasGeometry.solar_gap, lower_charge]

/-- At least 1.09 percent less commanded delta-v in the validated terminal
program. This ratio is invariant under the common exact SI conversion. -/
theorem relative_cost_saving (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ dataError)
    (hb : ∀ i, |bb i-b i| ≤ dataError) (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa hh bb y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Cost c x < (9891/10000:ℝ)*Cost c y := by
  have hg := cost_gap hh bb he hb y hy hbox
  rw [cost_value] at hg ⊢
  linarith

def speed : ℝ := Real.sqrt (TerminalData.speedSquared:ℝ)
def timeUnit : ℝ := Real.sqrt ((FreeResponse.lengthUnit:ℝ)^3/132712440018000000000)
def maximumBurnCost : ℝ := (1/10000)*timeUnit/50
def costScale : ℝ := maximumBurnCost/c 0

theorem speed_pos : 0 < speed := by
  exact Real.sqrt_pos.mpr (by norm_num [TerminalData.speedSquared])

theorem speed_time : speed*timeUnit = (FreeResponse.lengthUnit:ℝ) := by
  unfold speed timeUnit
  rw [← Real.sqrt_mul (by norm_num [TerminalData.speedSquared])]
  norm_num [TerminalData.speedSquared, FreeResponse.lengthUnit]

theorem maximumBurnCost_formula : maximumBurnCost = speed*(BurnSensitivity.burnScale:ℝ) := by
  have hs : speed^2 = (TerminalData.speedSquared:ℝ) :=
    Real.sq_sqrt (by norm_num [TerminalData.speedSquared])
  have ht := speed_time
  have hp := speed_pos
  norm_num [maximumBurnCost, BurnSensitivity.burnScale, FreeResponse.lengthUnit,
    TerminalData.speedSquared] at hs ht ⊢
  nlinarith

theorem costScale_pos : 0 < costScale := by
  unfold costScale
  apply div_pos
  · rw [maximumBurnCost_formula]
    exact mul_pos speed_pos (by norm_num [BurnSensitivity.burnScale, FreeResponse.lengthUnit])
  · norm_num [c]

theorem costScale_value (j : Fin 18) : costScale*c j = maximumBurnCost := by
  have hc : c j = c 0 := by fin_cases j <;> rfl
  rw [hc]
  unfold costScale
  exact div_mul_cancel₀ _ (by norm_num [c])

theorem physical_propellant_saving (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ dataError)
    (hb : ∀ i, |bb i-b i| ≤ dataError) (y : Fin 18 → ℝ)
    (hy : IndependentFeasible axis kappa hh bb y)
    (hbox : ∀ j, 0 ≤ y j ∧ y j ≤ 1) {mass exhaust : ℝ}
    (hm : 0 < mass) (hexhaust : 0 < exhaust) :
    Propellant.consumedMass mass exhaust (Cost (fun _ => maximumBurnCost) x) <
      Propellant.consumedMass mass exhaust (Cost (fun _ => maximumBurnCost) y) := by
  have hg : Cost c x < Cost c y := by linarith [cost_gap hh bb he hb y hy hbox]
  have h := scaled_propellant_saving c x y costScale_pos hm hexhaust hg
  simpa only [costScale_value] using h

end GNC.Applications.OrbitalFuel.SolarSensitivityFuel
