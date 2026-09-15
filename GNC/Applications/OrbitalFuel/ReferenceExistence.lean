import GNC.Analysis.PolynomialExtension
import GNC.Analysis.PositiveExtension
import GNC.Dynamics.PolynomialOrbitInvariant
import GNC.Applications.OrbitalFuel.ValidatedReference

/-! Whole-horizon existence of the lifted solar reference, obtained from the
already checked polynomial step certificates and released Picard--Lindelof.
The clipped construction is proved to satisfy the original polynomial ODE.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ReferenceExistence
open GNC.PolynomialODE GNC.PolynomialOrbit ValidatedReference
open PolynomialReference

theorem regions : ∀ j : Fin 32, (steps j).region = 4/3 := by decide +kernel

theorem sequence_region (j : ℕ) (hj : j < 32) : (ValidatedReference.sequence j).region ≤ (4/3:ℚ) := by
  simp only [ValidatedReference.sequence, dif_pos hj, regions, le_refl]

theorem slope_bound (i : Fin 5) : ((field alpha i).slope (4/3):ℝ) ≤ 32 := by
  have h := field_slope (a := alpha) (by norm_num [alpha]) i
  exact_mod_cast h

theorem magnitude_bound (i : Fin 5) : ((field alpha i).majorant (4/3):ℝ) ≤ 16 := by
  fin_cases i <;> norm_num [field, Expr.majorant, alpha]

/-- The exact lifted reference exists for every time in the mission, with
the specified initial state. This is an existence theorem, not an assumption
that an externally computed curve already solves the ODE. -/
theorem exists_reference :
    ∃ x : ℝ → Fin 5 → ℝ, Continuous x ∧ x 0 = initial ∧
      ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt x (rate (alpha:ℝ) (x t)) t := by
  obtain ⟨x,hx,hi,hd⟩ := exists_solution_of_chain ValidatedReference.sequence (field alpha) 32
    (h := 3/160) (R := 4/3) (by norm_num) (by norm_num) (by norm_num)
    sequence_valid sequence_duration sequence_join sequence_region
    32 16 slope_bound magnitude_bound initial initial_error
  refine ⟨x,hx,hi,?_⟩
  intro t ht
  have h := hd t (by norm_num at ht ⊢; exact ht)
  simpa only [field_correct] using h

/-- The physical inverse-square, tangential-thrust reference exists and
avoids collision for the whole mission. Its continuous representative stays
away from zero also outside the horizon; the ODE is required on [0,0.6]. -/
theorem exists_physical_reference :
    ∃ w : ℝ → Fin 4 → ℝ, Continuous w ∧ (∀ t, 0 < radius (w t)) ∧
      w 0 = ![4/5,0,0,Real.sqrt (3/2)] ∧
      ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t := by
  obtain ⟨z,hz,hz₀,hdz⟩ := exists_reference
  have hc := constraint_preserved z hz hdz (by
    rw [hz₀]
    change (((4/5:ℝ)^2+0^2)*(5/4)^2-1)=0
    norm_num)
  have hu := inverse_pos_on z hz (by rw [hz₀]; change (0:ℝ)<5/4; norm_num) hc
  let w := fun t => project (z t)
  have hw : Continuous w := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun t => z t 0)
      exact (continuous_apply 0).comp hz
    · change Continuous (fun t => z t 1)
      exact (continuous_apply 1).comp hz
    · change Continuous (fun t => z t 2)
      exact (continuous_apply 2).comp hz
    · change Continuous (fun t => z t 3)
      exact (continuous_apply 3).comp hz
  have hr (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (3/5)) : 0 < radius (w t) :=
    radius_pos_of_constraint (hc t ht)
  have hdw (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (3/5)) :
      HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t :=
    project_derivative (hdz t ht) (hc t ht) (hu t ht)
  have hrc : Continuous radius := by unfold radius; fun_prop
  obtain ⟨v,hv,hvp,hve⟩ := GNC.PositiveExtension.exists_positive w hw radius hrc (by norm_num) hr
  refine ⟨v,hv,hvp,?_,?_⟩
  · rw [(hve 0 (by constructor <;> norm_num)).self_of_nhds]
    simp [w, project, hz₀, initial]
  · intro t ht
    rw [(hve t ht).self_of_nhds]
    exact (hdw t ht).congr_of_eventuallyEq (hve t ht)

end GNC.Applications.OrbitalFuel.ReferenceExistence
