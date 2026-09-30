import GNC.Analysis.DysonTranslation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Translation remainders retaining the time at which rotation error occurs.
The position weight is the exact remaining integration time, not a guessed
fraction of the horizon. The rotation remainder can be any continuous bound.
-/
noncomputable section
open Set
namespace GNC.Dyson
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]

theorem doubleIntegral_weight (f : ℝ → E) (hf : Continuous f) (S : ℝ) :
    (∫ s in (0 : ℝ)..S, ∫ r in (0 : ℝ)..s, f r) =
      ∫ s in (0 : ℝ)..S, (S-s) • f s := by
  have hd (t : ℝ) : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, f r) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hc : Continuous (fun s => ∫ r in (0 : ℝ)..s, f r) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have h := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (a := 0) (b := S) (u := fun t : ℝ => S-t) (u' := fun _ => (-1 : ℝ))
    (v := fun s => ∫ r in (0 : ℝ)..s, f r) (v' := f)
    (by fun_prop) hc.continuousOn
    (fun t _ => by simpa using (hasDerivAt_const t S).sub (hasDerivAt_id t))
    (fun t _ => hd t) intervalIntegrable_const (hf.intervalIntegrable 0 S)
  simpa using h.symm

theorem physical_position_error_integral (B a v p : ℝ → E)
    (hB : Continuous B) (ha : Continuous a) (hv : Continuous v)
    (T : ℝ) (hp : ∀ t, HasDerivAt p (T • v t) t) (hp0 : p 0 = 0)
    (N : ℕ) (S : ℝ) :
    p S - T • positionApprox B a (N+1) S =
      T • ∫ s in (0 : ℝ)..S, v s - velocityApprox B a N s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hp s)
    ((continuous_const.smul hv).intervalIntegrable 0 S)
  simp only [hp0, sub_zero, intervalIntegral.integral_smul] at hi
  rw [intervalIntegral.integral_sub (hv.intervalIntegrable 0 S)
    ((velocityApprox_continuous B a hB ha N).intervalIntegrable 0 S), smul_sub, hi]
  rfl

/-- Weighted velocity and physical-position bounds at any horizon. `δ` bounds
the rotation error pointwise and `u` bounds the acceleration pointwise.
Both are explicit functions, not uniform endpoint allowances. -/
theorem translation_weighted_bound (B R a v p : ℝ → E) (δ u : ℝ → ℝ)
    (hB : Continuous B) (hR : Continuous R) (ha : Continuous a)
    (hδ : Continuous δ) (hu : Continuous u)
    (hv : ∀ t, HasDerivAt v (R t * a t) t) (hv0 : v 0 = 0)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hp : ∀ t, HasDerivAt p (T • v t) t) (hp0 : p 0 = 0) (N : ℕ)
    (herr : ∀ t ∈ Icc 0 S, ‖R t - approx B N t‖ ≤ δ t)
    (hacc : ∀ t ∈ Icc 0 S, ‖a t‖ ≤ u t) :
    ‖v S - velocityApprox B a N S‖ ≤ ∫ s in (0 : ℝ)..S, δ s * u s ∧
    ‖p S - T • positionApprox B a (N+1) S‖ ≤
      T * ∫ s in (0 : ℝ)..S, (S-s) * (δ s * u s) := by
  have hc : Continuous (fun s => (R s - approx B N s) * a s) :=
    (hR.sub (approx_continuous B hB N)).mul ha
  have hb (s : ℝ) (hs : s ∈ Icc 0 S) :
      ‖(R s - approx B N s) * a s‖ ≤ δ s * u s :=
    (norm_mul_le _ _).trans (mul_le_mul (herr s hs) (hacc s hs)
      (norm_nonneg _) ((norm_nonneg _).trans (herr s hs)))
  constructor
  · rw [velocity_error_integral B R a v hB hR ha hv hv0 N S]
    exact intervalIntegral.norm_integral_le_of_norm_le hS
      (MeasureTheory.ae_of_all _ (fun s hs => hb s ⟨hs.1.le, hs.2⟩))
      ((hδ.mul hu).intervalIntegrable 0 S)
  · have hvc : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hv t).continuousAt)
    rw [physical_position_error_integral B a v p hB ha hvc T hp hp0 N S]
    simp_rw [velocity_error_integral B R a v hB hR ha hv hv0 N]
    rw [doubleIntegral_weight _ hc S, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]
    apply mul_le_mul_of_nonneg_left _ hT
    apply intervalIntegral.norm_integral_le_of_norm_le hS
      (MeasureTheory.ae_of_all _ (fun s hs => ?_))
      (((continuous_const.sub continuous_id).mul (hδ.mul hu)).intervalIntegrable 0 S)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    exact mul_le_mul_of_nonneg_left (hb s ⟨hs.1.le, hs.2⟩) (sub_nonneg.mpr hs.2)

end GNC.Dyson
