import GNC.Applications.OrbitalFuel.PolynomialReference
import GNC.Applications.OrbitalFuel.ReferenceEnvelopes

/-! Whole-horizon enclosure of the existing planar heliocentric reference.
The proposal program is not trusted. PolynomialReference supplies kernel-
checked rational defects, regions, and joins; PolynomialChain supplies the
continuous-time argument. This does not yet certify the variational kernels
or the chaser's reachable set.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.ValidatedReference
open GNC.PolynomialODE GNC.PolynomialOrbit
open PolynomialReference

theorem alpha_matches_mission : (alpha:ℝ) = Reference.solarThrust := by
  norm_num [alpha, Reference.solarThrust, Reference.solarLength, Reference.solarMu]

theorem physical_error_scales :
    Reference.solarLength/(10^19:ℝ) < 15/10^9 ∧ (29785:ℝ)/10^19 < 3/10^15 := by
  norm_num [Reference.solarLength]

/-- The checker rejects deleting the truncation-error allowance. -/
theorem rejects_zero_defect : ¬ ({step0 with defect := 0} : Step 5).Valid (field alpha) := by
  decide +kernel

def initial : Fin 5 → ℝ := ![4/5,0,0,Real.sqrt (3/2),5/4]

def sequence (j : ℕ) : Step 5 := if hj : j < 32 then steps ⟨j,hj⟩ else step0

theorem sequence_valid (j : ℕ) (hj : j < 32) : (sequence j).Valid (field alpha) := by
  simpa [sequence, hj] using steps_valid ⟨j,hj⟩

theorem sequence_duration (j : ℕ) (hj : j < 32) : (sequence j).duration = 3/160 := by
  simpa [sequence, hj] using durations ⟨j,hj⟩

theorem sequence_join (j : ℕ) (hj : j+1 < 32) : Compatible (sequence j) (sequence (j+1)) := by
  have hj' : j < 32 := by omega
  simpa [sequence, hj, hj'] using joins ⟨j,by omega⟩

theorem sequence_error (j : ℕ) (hj : j < 32) : (sequence j).error < 1/10^19 := by
  simpa [sequence, hj] using errors ⟨j,hj⟩

theorem initial_error : ‖initial-curve (sequence 0).coefficients 0‖ ≤
    ((sequence 0).initialError:ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num [sequence, steps, step0])).mpr
  intro i
  fin_cases i <;> norm_num [initial, sequence, steps, step0, curve,
    GNC.Planning.PolynomialKernel.evaluate, Real.norm_eq_abs]
  rw [← Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
  apply abs_le.mpr
  constructor <;> nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3/2 by norm_num), Real.sqrt_nonneg (3/2)]

/-- Every time in [0,0.6] has a certified polynomial approximation with
componentwise normalized error below 10^-19, including inverse radius.
The statement quantifies over existing continuous solutions of the ODE. -/
theorem enclosure (x : ℝ → Fin 5 → ℝ) (hx : Continuous x)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt x (rate (alpha:ℝ) (x t)) t)
    (hi : x 0 = initial) :
    ∀ t ∈ Set.Icc (0:ℝ) (3/5), ∃ j : ℕ, j < 32 ∧ ∃ u ∈ Set.Icc (0:ℝ) (3/160),
      t = (j:ℝ)*(3/160)+u ∧ ‖x t-curve (sequence j).coefficients u‖ < 1/10^19 := by
  have hc := chain_sound sequence (field alpha) 32
    (show (0:ℚ) ≤ 3/160 by norm_num) sequence_valid sequence_duration sequence_join x hx
    (fun t ht => by
      have ht' : t ∈ Set.Icc (0:ℝ) (3/5) := by norm_num at ht ⊢; exact ht
      convert hd t ht' using 1
      funext i
      exact field_correct alpha (x t) i)
    (by rw [hi]; exact initial_error)
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) ((32:ℝ)*(3/160)) := by norm_num at ht ⊢; exact ht
  obtain ⟨j,hj,u,hu,he⟩ := grid_covers 32 (by norm_num : (0:ℝ) ≤ 3/160) (by norm_num) ht'
  refine ⟨j,hj,u,hu,he,?_⟩
  rw [he]
  have hb := hc j hj u (by norm_num at hu ⊢; exact hu)
  have herr : ((sequence j).error:ℝ) < (1:ℝ)/10^19 := by
    have hrat := sequence_error j hj
    have hcast := (Rat.cast_lt (K := ℝ)).mpr hrat
    norm_num at hcast ⊢
    exact hcast
  convert hb.trans herr using 1 <;> norm_num

/-- Transfer to the original planar inverse-square, tangential-thrust model.
The global noncollision hypothesis ensures continuity of the inverse-radius
lift; the differential equations are required only on the mission horizon. -/
theorem physical_enclosure (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0 < radius (w t))
    (hd : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) :
    ∀ t ∈ Set.Icc (0:ℝ) (3/5), ∃ j : ℕ, j < 32 ∧ ∃ u ∈ Set.Icc (0:ℝ) (3/160),
      t = (j:ℝ)*(3/160)+u ∧
        ‖lift (w t)-curve (sequence j).coefficients u‖ < 1/10^19 := by
  apply enclosure (fun t => lift (w t)) (lift_continuous hw hr)
    (fun t ht => lift_derivative (hd t ht) (hr t))
  rw [hi]
  norm_num [lift, radius, initial]
  exact ⟨rfl,rfl⟩

end GNC.Applications.OrbitalFuel.ValidatedReference
