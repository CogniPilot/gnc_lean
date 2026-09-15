import GNC.Applications.OrbitalFuel.ComparatorPrefixData
import GNC.Applications.OrbitalFuel.ChaserReferenceData
import GNC.Analysis.SwitchedInputBound

/-! Soundness of the comparator's stored prefix inequalities, including
continuous time, the pointing-cap radius and exact command differences.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.Applications.OrbitalFuel.ComparatorPrefix
open GNC PolynomialAffine PolynomialOrbit PolynomialOrbitTransition PolynomialBurn Set Matrix

def impulseReal (t : ℝ) : ℝ := ∑ j : Fin 18,
  (min t (burnFinish j:ℝ)-min t (burnStart j:ℝ))*(rate j:ℝ)

theorem impulseReal_cast (t : ℚ) : impulseReal (t:ℝ) = (impulse t:ℝ) := by
  unfold impulseReal impulse
  push_cast
  rfl

theorem rate_nonneg (j : Fin 18) : (0:ℝ) ≤ (rate j:ℝ) := by
  have hy := (SolarComparatorData.in_box j).1
  have hb : (0:ℚ) ≤ beta := by
    norm_num [beta,BurnSensitivity.burnScale,FreeResponse.lengthUnit]
  exact_mod_cast mul_nonneg hb (add_nonneg (abs_nonneg _)
    (mul_nonneg hy (by norm_num [pointingRadius])))

theorem impulseReal_nonneg {t : ℝ} : 0 ≤ impulseReal t := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sub_nonneg.mpr (min_le_min_left t (by
    norm_num [burnFinish,burnStart]))) (rate_nonneg j)

theorem impulseReal_monotone : Monotone impulseReal := by
  intro s t hst
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (rate_nonneg j)
  simpa only [min_comm] using GNC.ArcGronwall.duration_mono
    (a := (burnStart j:ℝ)) (b := (burnFinish j:ℝ)) (by norm_num [burnStart,burnFinish]) hst

theorem axis_unit : SharedBiasExample.axis ⬝ᵥ SharedBiasExample.axis = 1 := by
  norm_num [SharedBiasExample.axis,dotProduct,Fin.sum_univ_succ]

theorem axis_in_cap : SharedBiasExample.axis ∈
    ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa := by
  exact ⟨axis_unit,by rw [axis_unit]; norm_num [SharedBiasCertificates.Solar.kappa]⟩

theorem pointing_bound (q : Vec3)
    (hq : q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    GNC.enorm (q-SharedBiasExample.axis) ≤ (pointingRadius:ℝ) := by
  apply ThrustSupport.cap_in_chord_ball _ _ _ _ axis_unit hq
  · norm_num [pointingRadius]
  · norm_num [pointingRadius,SharedBiasCertificates.Solar.kappa]

theorem command_difference (j : Fin 18) (q : Vec3)
    (hq : q ∈ ThrustSupport.Cap SharedBiasExample.axis SharedBiasCertificates.Solar.kappa) :
    GNC.enorm (SolarComparator.plan j • rotate (SharedBiasGeometry.cycleRotation j) q-
      RetainedPhysical.commands SharedBiasExample.axis j) ≤
      |(SolarComparatorData.y j:ℝ)-(RetainedNormData.fractions j:ℝ)|+
        (SolarComparatorData.y j:ℝ)*(pointingRadius:ℝ) := by
  have he : SolarComparator.plan j • rotate (SharedBiasGeometry.cycleRotation j) q-
      RetainedPhysical.commands SharedBiasExample.axis j =
      ((SolarComparatorData.y j:ℝ)-(RetainedNormData.fractions j:ℝ)) •
        rotate (SharedBiasGeometry.cycleRotation j) SharedBiasExample.axis+
      (SolarComparatorData.y j:ℝ) •
        rotate (SharedBiasGeometry.cycleRotation j) (q-SharedBiasExample.axis) := by
    rw [RetainedPhysical.commands,← RetainedNorm.candidate_matches j]
    simp only [SolarComparator.plan,rotate,Matrix.mulVec_sub,smul_sub,sub_smul]
    module
  rw [he]
  have h := GNC.enorm_add_le
    (((SolarComparatorData.y j:ℝ)-(RetainedNormData.fractions j:ℝ)) •
      rotate (SharedBiasGeometry.cycleRotation j) SharedBiasExample.axis)
    ((SolarComparatorData.y j:ℝ) • rotate (SharedBiasGeometry.cycleRotation j) (q-SharedBiasExample.axis))
  rw [GNC.enorm_smul,GNC.enorm_smul,GNC.rotate_enorm,GNC.rotate_enorm,
    ThrustSupport.unit_enorm _ axis_unit,mul_one,
    abs_of_nonneg (show (0:ℝ) ≤ (SolarComparatorData.y j:ℝ) by
      exact_mod_cast (SolarComparatorData.in_box j).1)] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (pointing_bound q hq)
    (by exact_mod_cast (SolarComparatorData.in_box j).1)))

theorem nominal_enclosure (n : Fin 68) {t : ℝ}
    (ht : t ∈ Icc ((RetainedNormData.pieces n).start:ℝ) ((RetainedNormData.pieces n).finish:ℝ)) :
    GNC.enorm ((RetainedNorm.lengthScale:ℝ) •
      (RetainedNormData.pieces n).response 0 t SharedBiasExample.axis) ≤
      (ComparatorPrefixData.nominalMetres n:ℝ) := by
  have hx : |(t-((RetainedNormData.pieces n).offset:ℝ))-(center n:ℝ)| ≤ (radius n:ℝ) := by
    unfold center radius
    push_cast
    exact abs_le.mpr ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
  have h := PolynomialTranslation.centered_bound (pairing (nominal n) (nominal n))
    (center n) (radius n) hx
  rw [pairing_value,dot_self_lengthSq,← GNC.enorm_sq,abs_of_nonneg (sq_nonneg _)] at h
  have hs : (PolynomialBounds.bound (PolynomialTranslation.translate (center n)
      (pairing (nominal n) (nominal n))) (radius n):ℝ) ≤
      ((ComparatorPrefixData.nominalMetres n:ℝ)/(RetainedNorm.lengthScale:ℝ))^2 := by
    exact_mod_cast (ComparatorPrefixData.valid n).2.1
  have hnon : (0:ℝ) ≤ (ComparatorPrefixData.nominalMetres n:ℝ) := by
    exact_mod_cast (ComparatorPrefixData.valid n).1
  have hn : GNC.enorm (value (nominal n) (t-((RetainedNormData.pieces n).offset:ℝ))) ≤
      (ComparatorPrefixData.nominalMetres n:ℝ)/(RetainedNorm.lengthScale:ℝ) := by
    have hp : (0:ℝ) ≤ (ComparatorPrefixData.nominalMetres n:ℝ)/(RetainedNorm.lengthScale:ℝ) :=
      div_nonneg hnon (by norm_num [RetainedNorm.lengthScale])
    nlinarith [GNC.enorm_nonneg (value (nominal n) (t-((RetainedNormData.pieces n).offset:ℝ)))]
  have he : (RetainedNormData.pieces n).response 0 t SharedBiasExample.axis =
      value (nominal n) (t-((RetainedNormData.pieces n).offset:ℝ)) := by
    simp [RetainedNorm.Piece.response,SharedBiasExample.axis,nominal,value_plus]
  rw [he,GNC.enorm_smul,abs_of_pos (show (0:ℝ) < (RetainedNorm.lengthScale:ℝ) by
    norm_num [RetainedNorm.lengthScale])]
  have hp := (le_div_iff₀ (show (0:ℝ) < (RetainedNorm.lengthScale:ℝ) by
    norm_num [RetainedNorm.lengthScale])).mp hn
  simpa only [mul_comm] using hp

/-- The finite checks cover every time in a cell, with the whole accumulated
input budget up to that cell's end. A dynamical comparison supplies its use. -/
theorem position_budget (n : Fin 68) {t : ℝ} (hzero : 0 ≤ t)
    (ht : t ≤ ((RetainedNormData.pieces n).finish:ℝ)) :
    (ComparatorPrefixData.nominalMetres n:ℝ)+1+3250+
      4*t*impulseReal t*(RetainedNorm.lengthScale:ℝ) < (proposedPosition:ℝ) := by
  have hcheck : (ComparatorPrefixData.nominalMetres n:ℝ)+1+3250+
      4*((RetainedNormData.pieces n).finish:ℝ)*
        impulseReal ((RetainedNormData.pieces n).finish:ℝ)*(RetainedNorm.lengthScale:ℝ) <
      (proposedPosition:ℝ) := by
    rw [impulseReal_cast]
    exact_mod_cast (ComparatorPrefixData.valid n).2.2
  have hb : 4*t*impulseReal t*(RetainedNorm.lengthScale:ℝ) ≤
      4*((RetainedNormData.pieces n).finish:ℝ)*
        impulseReal ((RetainedNormData.pieces n).finish:ℝ)*(RetainedNorm.lengthScale:ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) (impulseReal_monotone ht)
        impulseReal_nonneg (by have := hzero.trans ht; positivity))
      (by norm_num [RetainedNorm.lengthScale])
  linarith

end GNC.Applications.OrbitalFuel.ComparatorPrefix
