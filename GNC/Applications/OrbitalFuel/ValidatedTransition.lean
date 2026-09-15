import GNC.Applications.OrbitalFuel.PolynomialTransition
import GNC.Applications.OrbitalFuel.ValidatedReference
import GNC.Dynamics.PlanarGravityFlow

/-! Continuous enclosure of the joint solar reference and its two transition
blocks. All 32 polynomial defects and 31 jumps are checked by Lean. This
closes a transition approximation obligation; burn quadrature and the full
nonlinear chaser tube remain separate obligations.
-/
noncomputable section
namespace GNC.Applications.OrbitalFuel.ValidatedTransition
open GNC.PolynomialODE GNC.PolynomialOrbitTransition
open PolynomialTransition

def initial : Fin 25 → ℝ := pack ValidatedReference.initial 1 1
def sequence (j : ℕ) : BoxStep 25 := if hj : j < 32 then steps ⟨j,hj⟩ else step0

theorem sequence_valid (j : ℕ) (hj : j < 32) : (sequence j).Valid (field alpha) := by
  simpa [sequence, hj] using steps_valid ⟨j,hj⟩

theorem sequence_duration (j : ℕ) (hj : j < 32) : (sequence j).duration = 3/160 := by
  simpa [sequence, hj] using durations ⟨j,hj⟩

theorem sequence_join (j : ℕ) (hj : j+1 < 32) :
    (sequence j).Compatible (sequence (j+1)) := by
  have hj' : j < 32 := by omega
  simpa [sequence, hj, hj'] using joins ⟨j,by omega⟩

theorem sequence_reference_error (j : ℕ) (hj : j < 32) (i : Fin 25) (hi : i.val < 5) :
    ((sequence j).error i:ℝ) < 1/10^19 := by
  have hrat : (sequence j).error i < 1/10^19 := by
    simpa [sequence, hj] using reference_error ⟨j,hj⟩ i hi
  have hcast := (Rat.cast_lt (K := ℝ)).mpr hrat
  norm_num at hcast ⊢
  exact hcast

theorem sequence_transition_error (j : ℕ) (hj : j < 32) (i : Fin 25) (hi : 5 ≤ i.val) :
    ((sequence j).error i:ℝ) < 1/10^16 := by
  have hrat : (sequence j).error i < 1/10^16 := by
    simpa [sequence, hj] using transition_error ⟨j,hj⟩ i hi
  have hcast := (Rat.cast_lt (K := ℝ)).mpr hrat
  norm_num at hcast ⊢
  exact hcast

set_option maxHeartbeats 4000000 in
theorem initial_error (i : Fin 25) : |initial i-curve (sequence 0).coefficients 0 i| ≤
    ((sequence 0).initialError i:ℝ) := by
  fin_cases i <;> norm_num [initial, ValidatedReference.initial, sequence, steps,
    step0, pack, PolynomialTransition.initialError, curve, GNC.Planning.PolynomialKernel.evaluate,
    Matrix.one_apply]
  rw [← Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
  apply abs_le.mpr
  constructor <;> nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3/2 by norm_num), Real.sqrt_nonneg (3/2)]

/-- Existing reference and transition solutions are enclosed for every real
time in the mission, not only the step boundaries. Matrix errors are entrywise
in normalized Cartesian coordinates; they are not operator-norm bounds. -/
theorem enclosure (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt z (GNC.PolynomialOrbit.rate alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t) * F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t) * H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) (3/5), ∃ j : ℕ, j < 32 ∧ ∃ u ∈ Set.Icc (0:ℝ) (3/160),
      t = (j:ℝ)*(3/160)+u ∧
      (∀ i : Fin 5, |z t i-curve (sequence j).coefficients u (referenceIndex i)| < 1/10^19) ∧
      (∀ i k : Fin 4, |F t i k-curve (sequence j).coefficients u (planeIndex i k)| < 1/10^16) ∧
      (∀ i k : Fin 2, |H t i k-curve (sequence j).coefficients u (normalIndex i k)| < 1/10^16) := by
  have hc := box_chain_sound sequence (field alpha) 32 (3/160)
    sequence_valid sequence_duration sequence_join (fun t => pack (z t) (F t) (H t))
    (pack_continuous hz hF hH)
    (fun t ht => by
      have ht' : t ∈ Set.Icc (0:ℝ) (3/5) := by norm_num at ht ⊢; exact ht
      exact joint_derivative alpha (hdz t ht') (hdF t ht') (hdH t ht'))
    (by
      change ∀ i, |pack (z 0) (F 0) (H 0) i-curve (sequence 0).coefficients 0 i| ≤
        ((sequence 0).initialError i:ℝ)
      rw [hiz,hiF,hiH]
      exact initial_error)
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) ((32:ℝ)*(3/160)) := by norm_num at ht ⊢; exact ht
  obtain ⟨j,hj,u,hu,he⟩ := grid_covers 32 (by norm_num : (0:ℝ) ≤ 3/160) (by norm_num) ht'
  have hb := hc j hj u (by norm_num at hu ⊢; exact hu)
  have he' : (j:ℝ)*(↑(3/160:ℚ))+u = t := by norm_num; exact he.symm
  rw [he'] at hb
  refine ⟨j,hj,u,hu,he,?_,?_,?_⟩
  · intro i
    have h := (hb (referenceIndex i)).trans (sequence_reference_error j hj (referenceIndex i) (by
      simpa [referenceIndex] using i.isLt))
    simpa only [pack_reference] using h
  · intro i k
    have h := (hb (planeIndex i k)).trans (sequence_transition_error j hj (planeIndex i k) (by
      dsimp [planeIndex]; omega))
    simpa only [pack_plane] using h
  · intro i k
    have h := (hb (normalIndex i k)).trans (sequence_transition_error j hj (normalIndex i k) (by
      dsimp [normalIndex]; omega))
    simpa only [pack_normal] using h

/-- The signed-transpose polynomial has the same entrywise error allowance
as the forward transition; no numerical matrix inversion is trusted. -/
theorem inverse_enclosure (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdz : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt z (GNC.PolynomialOrbit.rate alpha (z t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t) * F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t) * H t) t)
    (hiz : z 0 = ValidatedReference.initial) (hiF : F 0 = 1) (hiH : H 0 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) (3/5), ∃ j : ℕ, j < 32 ∧ ∃ u ∈ Set.Icc (0:ℝ) (3/160),
      t = (j:ℝ)*(3/160)+u ∧
      (∀ i k : Fin 4, |(F t)⁻¹ i k -
        planeInverse (fun a b => curve (sequence j).coefficients u (planeIndex a b)) i k| < 1/10^16) ∧
      (∀ i k : Fin 2, |(H t)⁻¹ i k -
        normalInverse (fun a b => curve (sequence j).coefficients u (normalIndex a b)) i k| < 1/10^16) := by
  intro t ht
  obtain ⟨j,hj,u,hu,he,_,hf,hh⟩ := enclosure z F H hz hF hH hdz hdF hdH hiz hiF hiH t ht
  refine ⟨j,hj,u,hu,he,?_,?_⟩
  · rw [plane_inverse z F hdF hiF t ht]
    exact planeInverse_error _ _ hf
  · rw [normal_inverse z H hdH hiH t ht]
    exact normalInverse_error _ _ hh

/-- Transfer to the original planar inverse-square/tangential-reference model.
The reference exists and is globally noncolliding; the equations are imposed
only on the mission horizon. Fundamental matrices start at the identity. -/
theorem physical_enclosure (w : ℝ → Fin 4 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hw : Continuous w) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t, 0 < GNC.PolynomialOrbit.radius (w t))
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt w (GNC.PolynomialOrbit.physicalRate alpha (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt F (planeGenerator (GNC.PolynomialOrbit.lift (w t)) * F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5),
      HasDerivAt H (normalGenerator (GNC.PolynomialOrbit.lift (w t)) * H t) t)
    (hiw : w 0 = ![4/5,0,0,Real.sqrt (3/2)]) (hiF : F 0 = 1) (hiH : H 0 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) (3/5), ∃ j : ℕ, j < 32 ∧ ∃ u ∈ Set.Icc (0:ℝ) (3/160),
      t = (j:ℝ)*(3/160)+u ∧
      (∀ i : Fin 5, |GNC.PolynomialOrbit.lift (w t) i-
        curve (sequence j).coefficients u (referenceIndex i)| < 1/10^19) ∧
      (∀ i k : Fin 4, |F t i k-curve (sequence j).coefficients u (planeIndex i k)| < 1/10^16) ∧
      (∀ i k : Fin 2, |H t i k-curve (sequence j).coefficients u (normalIndex i k)| < 1/10^16) := by
  apply enclosure (fun t => GNC.PolynomialOrbit.lift (w t)) F H
    (GNC.PolynomialOrbit.lift_continuous hw hr) hF hH
    (fun t ht => GNC.PolynomialOrbit.lift_derivative (hdw t ht) (hr t)) hdF hdH ?_ hiF hiH
  change GNC.PolynomialOrbit.lift (w 0) = ValidatedReference.initial
  rw [hiw]
  norm_num [GNC.PolynomialOrbit.lift, GNC.PolynomialOrbit.radius, ValidatedReference.initial]
  exact ⟨rfl,rfl⟩

end GNC.Applications.OrbitalFuel.ValidatedTransition
