import GNC.Analysis.ArcGronwall
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Parameter differentiation of an actual right linear ODE. The quadratic
remainder estimate proves the parameter derivative without assuming any
parameter regularity of the solution family. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace GNC.Magnus
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem foh_parameter_remainder_bound
    (A B : ℝ → E) (R : ℝ → ℝ → E) (Z : ℝ → E)
    {T e Ka Kb M : ℝ} (hT : 0 ≤ T) (he : |e| ≤ 1)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hM : 0 ≤ M)
    (hA : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ Ka)
    (hB : ∀ t ∈ Icc 0 T, ‖B t‖ ≤ Kb)
    (hZb : ∀ t ∈ Icc 0 T, ‖Z t‖ ≤ M)
    (hR : ∀ q t, t ∈ Icc 0 T →
      HasDerivAt (R q) (R q t * (A t + q • B t)) t)
    (hR0 : ∀ q, R q 0 = 1) (hZ0 : Z 0 = 0)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z t * A t + R 0 t * B t) t) :
    ‖R e T - R 0 T - e • Z T‖ ≤ (M * Kb * T * Real.exp ((Ka + Kb) * T)) * e ^ 2 := by
  let F : ℝ → E := fun t => R e t - R 0 t - e • Z t
  let D : ℝ → E := fun t => F t * (A t + e • B t) + (e ^ 2) • (Z t * B t)
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt F (D t) t := by
    have h := ((hR e t ht).sub (hR 0 t ht)).sub ((hZ t ht).const_smul e)
    convert h using 1
    dsimp [D, F]
    simp only [zero_smul, add_zero, sub_mul, mul_add, mul_smul_comm, smul_mul_assoc,
      smul_add, smul_sub, smul_smul, pow_two]
    module
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) : ‖D t‖ ≤ (Ka + Kb) * ‖F t‖ + e ^ 2 * (M * Kb) := by
    have ht' := Ico_subset_Icc_self ht
    have hc : ‖A t + e • B t‖ ≤ Ka + Kb := by
      calc
        _ ≤ ‖A t‖ + ‖e • B t‖ := norm_add_le _ _
        _ = ‖A t‖ + |e| * ‖B t‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ Ka + 1 * Kb := add_le_add (hA t ht')
          (mul_le_mul he (hB t ht') (norm_nonneg _) (by norm_num))
        _ = _ := by ring
    calc
      ‖D t‖ ≤ ‖F t * (A t + e • B t)‖ + ‖(e ^ 2) • (Z t * B t)‖ := norm_add_le _ _
      _ ≤ ‖F t‖ * ‖A t + e • B t‖ + e ^ 2 * (‖Z t‖ * ‖B t‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg e)]
        exact add_le_add (norm_mul_le _ _) (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (sq_nonneg e))
      _ ≤ ‖F t‖ * (Ka + Kb) + e ^ 2 * (M * Kb) :=
        add_le_add (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (mul_le_mul (hZb t ht') (hB t ht') (norm_nonneg _) hM) (sq_nonneg e))
      _ = _ := by ring
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show ‖F 0‖ ≤ (0 : ℝ) by simp [F, hR0, hZ0]) hb T ⟨hT, le_rfl⟩
  have hu := GNC.ArcGronwall.gronwall_upper (δ := 0) (add_nonneg hKa hKb)
    (mul_nonneg (sq_nonneg e) (mul_nonneg hM hKb)) hT
  simp only [sub_zero] at hg
  calc
    _ ≤ _ := hg.trans hu
    _ = _ := by ring

/-- Differentiability in the parameter follows from the ODE and its initial
condition. Only time derivatives of the trajectories occur among the premises. -/
theorem foh_parameter_hasDerivAt
    (A B : ℝ → E) (R : ℝ → ℝ → E) (Z : ℝ → E)
    {T : ℝ} (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T))
    (hR : ∀ q t, t ∈ Icc 0 T →
      HasDerivAt (R q) (R q t * (A t + q • B t)) t)
    (hR0 : ∀ q, R q 0 = 1) (hZ0 : Z 0 = 0)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z t * A t + R 0 t * B t) t) :
    HasDerivAt (fun q => R q T) (Z T) 0 := by
  obtain ⟨Ka, ha⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨Kb, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  have hzcont : ContinuousOn Z (Icc 0 T) :=
    fun t ht => (hZ t ht).continuousAt.continuousWithinAt
  obtain ⟨M, hm⟩ := isCompact_Icc.exists_bound_of_continuousOn hzcont
  have ha0 : 0 ≤ Ka := (norm_nonneg _).trans (ha 0 ⟨le_rfl, hT⟩)
  have hb0 : 0 ≤ Kb := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hm0 : 0 ≤ M := (norm_nonneg _).trans (hm 0 ⟨le_rfl, hT⟩)
  have hbig : (fun q => R q T - R 0 T - q • Z T) =O[𝓝 0] (fun q : ℝ => q ^ 2) := by
    apply IsBigO.of_bound (M * Kb * T * Real.exp ((Ka + Kb) * T))
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with q hq
    have hq' : |q| ≤ 1 := (by simpa [Metric.mem_ball, Real.dist_eq] using hq : |q| < 1).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)] using
      foh_parameter_remainder_bound A B R Z hT hq' ha0 hb0 hm0 ha hb hm hR hR0 hZ0 hZ
  have hsmall := hbig.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))
  simpa only [hasDerivAt_iff_isLittleO, sub_zero] using hsmall

/-- Time derivative of the inverse of a right fundamental solution. -/
theorem foh_inverse_derivative (U : ℝ → Eˣ) (A : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val * A t) t) (t : ℝ) :
    HasDerivAt (fun s => ((U s)⁻¹).val) (-A t * ((U t)⁻¹).val) t := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (U t)).comp_hasDerivAt t (hU t)
  change HasDerivAt (fun s => Ring.inverse (U s).val) _ t at h
  simp only [Ring.inverse_unit] at h
  convert h using 1
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  simp only [← mul_assoc, neg_mul, Units.inv_mul, one_mul]

def fohConjugatedInput (U : ℝ → Eˣ) (B : ℝ → E) (t : ℝ) : E :=
  (U t).val * B t * ((U t)⁻¹).val

def fohSensitivityIntegral (U : ℝ → Eˣ) (B : ℝ → E) (t : ℝ) : E :=
  (∫ s in (0 : ℝ)..t, fohConjugatedInput U B s) * (U t).val

theorem foh_conjugatedInput_continuous (U : ℝ → Eˣ) (A B : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val * A t) t)
    (hB : Continuous B) : Continuous (fohConjugatedInput U B) := by
  have hu : Continuous (fun t => (U t).val) := continuous_iff_continuousAt.mpr
    (fun t => (hU t).continuousAt)
  have hi : Continuous (fun t => ((U t)⁻¹).val) := continuous_iff_continuousAt.mpr
    (fun t => (foh_inverse_derivative U A hU t).continuousAt)
  exact (hu.mul hB).mul hi

/-- The variation solution is constructed from a definite integral. -/
theorem foh_sensitivityIntegral_derivative (U : ℝ → Eˣ) (A B : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val * A t) t)
    (hB : Continuous B) (t : ℝ) :
    HasDerivAt (fohSensitivityIntegral U B)
      (fohSensitivityIntegral U B t * A t + (U t).val * B t) t := by
  have hc := foh_conjugatedInput_continuous U A B hU hB
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert hp.mul (hU t) using 1
  simp only [fohSensitivityIntegral, fohConjugatedInput, mul_assoc, Units.inv_mul, mul_one]
  exact add_comm _ _

/-- Genuine parameter sensitivity of any actual family of invertible ODE
solutions. No parameter derivative or variation equation is assumed. -/
theorem foh_parameter_integral_hasDerivAt
    (A B : ℝ → E) (R : ℝ → ℝ → Eˣ) (hA : Continuous A) (hB : Continuous B)
    (hR : ∀ q t, HasDerivAt (fun s => (R q s).val)
      ((R q t).val * (A t + q • B t)) t)
    (hR0 : ∀ q, R q 0 = 1) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (fun q => (R q T).val) (fohSensitivityIntegral (R 0) B T) 0 := by
  have hu : ∀ t, HasDerivAt (fun s => (R 0 s).val) ((R 0 t).val * A t) t := by
    intro t
    simpa only [zero_smul, add_zero] using hR 0 t
  exact foh_parameter_hasDerivAt A B (fun q t => (R q t).val)
    (fohSensitivityIntegral (R 0) B) hT hA.continuousOn hB.continuousOn
    (fun q t _ => hR q t) (fun q => by simp [hR0])
    (by simp [fohSensitivityIntegral])
    (fun t _ => foh_sensitivityIntegral_derivative (R 0) A B hu hB t)

/-- Right trivialization converts the sensitivity ODE into the rotated input. -/
theorem foh_trivialized_sensitivity_derivative
    (U : ℝ → Eˣ) (A B Z : ℝ → E)
    (hU : ∀ t, HasDerivAt (fun s => (U s).val) ((U t).val * A t) t)
    {t : ℝ} (hZ : HasDerivAt Z (Z t * A t + (U t).val * B t) t) :
    HasDerivAt (fun s => Z s * ((U s)⁻¹).val) (fohConjugatedInput U B t) t := by
  convert hZ.mul (foh_inverse_derivative U A hU t) using 1
  dsimp [fohConjugatedInput]
  noncomm_ring

end GNC.Magnus
