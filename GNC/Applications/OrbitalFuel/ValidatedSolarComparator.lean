import GNC.Applications.OrbitalFuel.SolarComparator
import GNC.Applications.OrbitalFuel.ValidatedSolarFuel

/-! Nonemptiness of the independent-burn comparison program for the exact
continuous solar reference and variational flow. Its feasible witness pays
the same physical data-error allowances used in the universal cost bound.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.ValidatedSolarComparator
open GNC GNC.SharedBias GNC.PolynomialOrbitTransition
open SharedBiasExample (axis)
open SharedBiasCertificates.Solar

theorem feasible (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt z (GNC.PolynomialOrbit.rate PolynomialTransition.alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1) :
    IndependentFeasible axis kappa (BurnSensitivity.physicalH z F H)
      (ValidatedSolarFuel.physicalB z F H) SolarComparator.plan :=
  SolarComparator.feasible _ _
    (ValidatedSolarFuel.coefficient_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)
    (ValidatedSolarFuel.rhs_error z F H hz hF hH hdz hdF hdH hiz hiF hiH)

/-- The supplied plan belongs to the exact reference-dependent comparison
program. No comparator feasibility or terminal-coefficient bound is assumed.
Existence and noncollision of the reference remain physical hypotheses. -/
theorem physical_reference_feasible (w : ℝ → Fin 4 → ℝ)
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
    IndependentFeasible axis kappa
      (BurnSensitivity.physicalH (fun t => GNC.PolynomialOrbit.lift (w t)) F H)
      (ValidatedSolarFuel.physicalB (fun t => GNC.PolynomialOrbit.lift (w t)) F H)
      SolarComparator.plan := by
  let z := fun t => GNC.PolynomialOrbit.lift (w t)
  have hz : Continuous z := GNC.PolynomialOrbit.lift_continuous hw hr
  have hdz := fun t ht => GNC.PolynomialOrbit.lift_derivative (hdw t ht) (hr t)
  have hiz : z 0 = ValidatedReference.initial := by
    change GNC.PolynomialOrbit.lift (w 0) = ValidatedReference.initial
    rw [hiw]
    norm_num [GNC.PolynomialOrbit.lift, GNC.PolynomialOrbit.radius, ValidatedReference.initial]
    exact ⟨rfl,rfl⟩
  exact feasible z F H hz hF hH hdz hdF hdH hiz hiF hiH

end GNC.Applications.OrbitalFuel.ValidatedSolarComparator
