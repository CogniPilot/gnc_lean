import GNC.Applications.OrbitalFuel.SolarComparatorData
import GNC.Applications.OrbitalFuel.SolarSensitivityFuel
import GNC.Control.IndependentBias

/-! A concrete feasible solar independent-burn comparator, including the
same physical terminal-data allowances used in the fuel lower bound.
The cap support inequalities quantify over all directions, not samples.
-/
noncomputable section
open Matrix Finset
namespace GNC.Applications.OrbitalFuel.SolarComparator
open GNC GNC.SharedBias
open SharedBiasExample (axis)
open SharedBiasCertificates.Solar

def plan (j : Fin 18) : ℝ := (SolarComparatorData.y j : ℝ)

theorem in_box (j : Fin 18) : 0 ≤ plan j ∧ plan j ≤ 1 := by
  unfold plan
  exact_mod_cast SolarComparatorData.in_box j

theorem kappa_cast : (SolarComparatorData.kappa : ℝ) = kappa := by
  norm_num [SolarComparatorData.kappa, kappa]

theorem error_cast : (SolarComparatorData.error : ℝ) = SolarSensitivityFuel.dataError := by
  norm_num [SolarComparatorData.error, SolarSensitivityFuel.dataError]

theorem b_cast (i : Fin 12) : (SolarComparatorData.b i : ℝ) = b i := by
  fin_cases i <;> norm_num [SolarComparatorData.b, b]

theorem squared_support (i : Fin 12) (j : Fin 18) :
    lengthSq (h i j+(SolarComparatorData.ell i j:ℝ) • axis) ≤
      (SolarComparatorData.s i j:ℝ)^2 := by
  have hq := (SolarComparatorData.support_certificate i j).2.2
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hr
  simp only [BurnSensitivity.reported_matches] at hr
  simpa [lengthSq, axis] using hr

theorem budget (i : Fin 12) :
    (∑ j, plan j*((SolarComparatorData.s i j:ℝ)-(SolarComparatorData.ell i j:ℝ)*kappa))+
      SolarSensitivityFuel.dataError+(∑ j, plan j*SolarSensitivityFuel.dataError) ≤ b i := by
  have hr := (Rat.cast_le (K := ℝ)).mpr (SolarComparatorData.row_budget i)
  push_cast at hr
  simpa only [kappa_cast, error_cast, b_cast, plan] using hr

/-- Strict row slack remains after rounding and all terminal-data charges. -/
theorem budget_margin (i : Fin 12) :
    (∑ j, plan j*((SolarComparatorData.s i j:ℝ)-(SolarComparatorData.ell i j:ℝ)*kappa))+
      SolarSensitivityFuel.dataError+(∑ j, plan j*SolarSensitivityFuel.dataError)+
        (7/10^8:ℝ) ≤ b i := by
  have hr := (Rat.cast_le (K := ℝ)).mpr (SolarComparatorData.row_margin i)
  push_cast at hr
  simpa only [kappa_cast, error_cast, b_cast, plan] using hr

/-- One fixed rational burn plan is feasible for every terminal program
within the validated vector and right-hand-side error allowances. -/
theorem feasible_with_margin (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ SolarSensitivityFuel.dataError)
    (hb : ∀ i, |bb i-b i| ≤ SolarSensitivityFuel.dataError) :
    IndependentFeasible axis kappa hh (fun i => bb i-7/10^8) plan := by
  apply independent_feasible_of_errors axis kappa hh h
    (fun _ _ => SolarSensitivityFuel.dataError) (fun i => bb i-7/10^8) (fun i => b i-7/10^8)
    (fun _ => SolarSensitivityFuel.dataError) plan he
    (fun i => by
      rw [show (bb i-7/10^8)-(b i-7/10^8) = bb i-b i by ring]
      exact hb i) (fun j => (in_box j).1)
  apply independent_of_certificate axis kappa h _ plan
    (fun i j => (SolarComparatorData.ell i j:ℝ))
    (fun i j => (SolarComparatorData.s i j:ℝ)) (fun j => (in_box j).1)
  · intro i j
    exact_mod_cast (SolarComparatorData.support_certificate i j).1
  · intro i j
    exact_mod_cast (SolarComparatorData.support_certificate i j).2.1
  · exact squared_support
  · intro i
    linarith [budget_margin i]

theorem feasible (hh : Fin 12 → Fin 18 → Vec3) (bb : Fin 12 → ℝ)
    (he : ∀ i j, GNC.enorm (hh i j-h i j) ≤ SolarSensitivityFuel.dataError)
    (hb : ∀ i, |bb i-b i| ≤ SolarSensitivityFuel.dataError) :
    IndependentFeasible axis kappa hh bb plan := by
  intro i q hq
  exact (feasible_with_margin hh bb he hb i q hq).trans
    (sub_le_self _ (by norm_num))

end GNC.Applications.OrbitalFuel.SolarComparator
