import GNC.Applications.OrbitalComparison.JointErrorReference

/-! Shared exact reference and force budgets for both directional-STT charts.
These constants follow from the prescribed reference polynomial and its
checked oscillator defect. No numerical integration tolerance is used. -/
namespace GNC.OrbitalComparison.TDSTTReference
open JointErrorData Planning.PolynomialKernel

def phaseBound : ℚ := LieSTTData.Phase.harmonic1.error
def radialCoefficients : List ℚ :=
  [modelInput.K-(3231/25000)^2,-2*(3231/25000)*(1/200000),-(1/200000)^2]
def forceBound : ℚ := PolynomialBounds.bound radialCoefficients 1+1/200000

theorem phaseBound_nonnegative : 0≤phaseBound := by decide +kernel
theorem forceBound_nonnegative : 0≤forceBound := by decide +kernel

noncomputable section
open Set LieSTTOutput Matrix

theorem radial_value (t : ℝ) : PolynomialOrder.value radialCoefficients t=radialForce t := by
  simp only [radialCoefficients,radialForce,referenceRate,PolynomialOrder.value,
    List.map_cons,List.map_nil,evaluate,Rat.coe_castHom,Rat.cast_sub,Rat.cast_neg,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  ring

theorem magnitude_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |radialForce t|+1/200000≤(forceBound:ℝ) := by
  have h := PolynomialBounds.bound_sound radialCoefficients
    (h := 1) (show |t|≤((1:ℚ):ℝ) by simpa only [abs_of_nonneg ht.1,Rat.cast_one] using ht.2)
  change |PolynomialOrder.value radialCoefficients t|≤_ at h
  rw [radial_value] at h
  simpa only [forceBound,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    using add_le_add_left h (1/200000:ℝ)

theorem reference_error (x : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (exactReference t-value3 modelInput.reference x t)≤(phaseBound:ℝ) := by
  apply (JointErrorData.reference_error x ht).trans
  have hp : (0:ℝ)≤phaseBound := by exact_mod_cast phaseBound_nonnegative
  simpa only [phaseBound,mul_one] using mul_le_mul_of_nonneg_left ht.2 hp

theorem force_error (x : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (exactForce t-value3 modelInput.force x t)≤(forceBound:ℝ)*(phaseBound:ℝ) := by
  have hp : (0:ℝ)≤phaseBound := by exact_mod_cast phaseBound_nonnegative
  have h1 := mul_le_mul_of_nonneg_left ht.2 hp
  have h2 := mul_le_mul (magnitude_bound ht) h1 (mul_nonneg hp ht.1)
    (show (0:ℝ)≤forceBound by exact_mod_cast forceBound_nonnegative)
  apply (JointErrorData.force_error x ht).trans
  simpa only [phaseBound,mul_one,mul_assoc] using h2

theorem exact_force_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (exactForce t)≤(forceBound:ℝ) := by
  have h := enorm_add_le (radialForce t • exactReference t)
    ((1/200000:ℝ) • planarSpin (exactReference t))
  rw [enorm_smul,enorm_smul,exactReference_norm,
    abs_of_pos (by norm_num : (0:ℝ)<1/200000),mul_one] at h
  have hs : enorm (planarSpin (exactReference t))≤1 := by
    simpa only [exactReference_norm] using planarSpin_bound (exactReference t)
  change enorm (exactForce t)≤_ at h
  apply h.trans
  calc
    _≤|radialForce t|+1/200000 := by gcongr; linarith
    _≤(forceBound:ℝ) := magnitude_bound ht

theorem polynomial_force_bound (x : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    enorm (value3 modelInput.force x t)≤(forceBound:ℝ)*(1+(phaseBound:ℝ)) := by
  have he : value3 modelInput.force x t=exactForce t-
      (exactForce t-value3 modelInput.force x t) := by module
  rw [he]
  have h := enorm_add_le (exactForce t) (-(exactForce t-value3 modelInput.force x t))
  rw [enorm_neg] at h
  exact h.trans ((add_le_add (exact_force_bound ht) (force_error x ht)).trans_eq (by ring))

end
end GNC.OrbitalComparison.TDSTTReference
