import GNC.Analysis.ReferenceInteraction
import GNC.Analysis.STMComparison

/-! A complete differential-defect budget for a factored STM approximation.
The baseline and correction may both be approximate. No termination of a
Magnus series is assumed. Concrete numerical implementations must establish
the stated continuous defects, factor bounds, initial identity and gain.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.ReferenceInteraction
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
local notation "End" => V →L[ℝ] V

/-- The baseline's defect is multiplied by the correction's size, and the
correction's defect by the baseline's size. The actual physical transition
gain then transports their sum to an endpoint STM error bound. -/
theorem factored_stm_error_bound
    (Φ F : ℝ → Endˣ) (A₀ ΔA U H E : ℝ → End)
    {a b δF δU boundF boundU gain : ℝ} (hab : a ≤ b)
    (hδF : 0 ≤ δF) (hδU : 0 ≤ δU) (hboundF : 0 ≤ boundF)
    (hboundU : 0 ≤ boundU) (hgain : 0 ≤ gain)
    (hΦ : ∀ t, HasDerivAt (fun s => (Φ s).val) ((A₀ t+ΔA t)*(Φ t).val) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt (fun s => (F s).val) (A₀ t*(F t).val+H t) t)
    (hU : ∀ t ∈ Icc a b, HasDerivAt U (coefficient (F t) (ΔA t)*U t+E t) t)
    (hcF : Continuous (fun t => (F t).val)) (hcU : Continuous U)
    (hcH : Continuous H) (hcE : Continuous E)
    (hinit : (F a).val*U a = (Φ a).val)
    (hsizeF : ∀ t ∈ Icc a b, ‖(F t).val‖ ≤ boundF)
    (hsizeU : ∀ t ∈ Icc a b, ‖U t‖ ≤ boundU)
    (hdefectF : ∀ t ∈ Icc a b, ‖H t‖ ≤ δF)
    (hdefectU : ∀ t ∈ Icc a b, ‖E t‖ ≤ δU)
    (htransport : (∫ s in a..b, ‖DefectBound.kernel Φ b s‖) ≤ gain) :
    ‖(F b).val*U b-(Φ b).val‖ ≤ gain*(δF*boundU+boundF*δU) := by
  apply STMComparison.defect_bound Φ (fun t => A₀ t+ΔA t)
    (fun t => (F t).val*U t) (fun t => H t*U t+(F t).val*E t)
    hΦ hab (add_nonneg (mul_nonneg hδF hboundU) (mul_nonneg hboundF hδU))
    hgain ((hcH.mul hcU).add (hcF.mul hcE))
    (fun t ht => reconstruct_inexact_defect (hF t ht) (hU t ht)) hinit
    ?_ htransport
  intro t ht
  exact (inexact_defect_norm (F t) (U t) (H t) (E t)).trans
    (add_le_add
      (mul_le_mul (hdefectF t ht) (hsizeU t ht) (norm_nonneg _) hδF)
      (mul_le_mul (hsizeF t ht) (hdefectU t ht) (norm_nonneg _) hboundF))

/-- A conservative, explicit version requiring only a bound on the scaled
physical generator. Released mathlib Grönwall supplies the growth factor;
there is no unknown exact-transition gain among the hypotheses. -/
theorem factored_stm_error_bound_of_generator_norm
    (Φ F : ℝ → Endˣ) (A₀ ΔA U H E : ℝ → End)
    {a b L δF δU boundF boundU : ℝ} (hab : a ≤ b)
    (hδF : 0 ≤ δF) (hδU : 0 ≤ δU) (hboundF : 0 ≤ boundF)
    (hΦ : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (Φ s).val) ((A₀ t+ΔA t)*(Φ t).val) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt (fun s => (F s).val) (A₀ t*(F t).val+H t) t)
    (hU : ∀ t ∈ Icc a b, HasDerivAt U (coefficient (F t) (ΔA t)*U t+E t) t)
    (hinit : (F a).val*U a = (Φ a).val)
    (hsizeF : ∀ t ∈ Icc a b, ‖(F t).val‖ ≤ boundF)
    (hsizeU : ∀ t ∈ Icc a b, ‖U t‖ ≤ boundU)
    (hdefectF : ∀ t ∈ Icc a b, ‖H t‖ ≤ δF)
    (hdefectU : ∀ t ∈ Icc a b, ‖E t‖ ≤ δU)
    (hgenerator : ∀ t ∈ Icc a b, ‖A₀ t+ΔA t‖ ≤ L) :
    ‖(F b).val*U b-(Φ b).val‖ ≤
      (δF*boundU+boundF*δU) *
        (if L = 0 then b-a else (Real.exp (L*(b-a))-1)/L) := by
  have h := STMComparison.defect_bound_of_generator_norm
    (fun t => A₀ t+ΔA t) (fun t => (F t).val*U t)
    (fun t => (Φ t).val) (fun t => H t*U t+(F t).val*E t)
    (fun t ht => reconstruct_inexact_defect (hF t ht) (hU t ht)) hΦ hinit
    hgenerator (δ := δF*boundU+boundF*δU)
    (fun t ht => (inexact_defect_norm (F t) (U t) (H t) (E t)).trans
      (add_le_add
        (mul_le_mul (hdefectF t ht) (hsizeU t ht) (norm_nonneg _) hδF)
        (mul_le_mul (hsizeF t ht) (hdefectU t ht) (norm_nonneg _) hboundF)))
    b ⟨hab,le_rfl⟩
  simpa only [STMComparison.defect_gain_formula] using h

end GNC.ReferenceInteraction
