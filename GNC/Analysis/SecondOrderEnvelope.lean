import GNC.Control.IntegralTube
import Mathlib.Analysis.Calculus.MeanValue

/-! A time-dependent second-order enclosure with a proved first-exit closure.
Polynomial supersolutions give rational certificates without evaluating a
matrix exponential or relying on sampled trajectory maxima. -/
noncomputable section
open Set
namespace GNC.SecondOrderEnvelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The acceleration bound is needed only inside the proposed position
envelope. Strict initial position slack closes that region automatically. -/
theorem barrier (p v acc : ℝ → E) (P V W : ℝ → ℝ) {T : ℝ}
    (hp : Continuous p) (hv : Continuous v)
    (hdp : ∀ t ∈ Icc 0 T, HasDerivAt p (v t) t)
    (hdv : ∀ t ∈ Icc 0 T, HasDerivAt v (acc t) t)
    (hP : ∀ t, HasDerivAt P (V t) t) (hV : ∀ t, HasDerivAt V (W t) t)
    (hiP : ‖p 0‖ < P 0) (hiV : ‖v 0‖ ≤ V 0)
    (ha : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P t → ‖acc t‖ ≤ W t) :
    ∀ t ∈ Icc 0 T, ‖p t‖ < P t ∧ ‖v t‖ ≤ V t := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have hprefix (t : ℝ) (ht : t ∈ Icc 0 T)
      (hregion : ∀ s ∈ Icc 0 t, ‖p s‖ ≤ P s) :
      ∀ s ∈ Icc 0 t, ‖v s‖ ≤ V s := by
    exact fun s hs => image_norm_le_of_norm_deriv_right_le_deriv_boundary hv.continuousOn
      (fun r hr => (hdv r ⟨hr.1,hr.2.le.trans ht.2⟩).hasDerivWithinAt)
      hiV hV (fun r hr => ha r ⟨hr.1,hr.2.le.trans ht.2⟩
        (hregion r (Ico_subset_Icc_self hr))) hs
  have hall := IntegralTube.prefix_closure (hp.norm.sub hcP)
    (sub_neg.mpr hiP) (a := 0) (b := T) (level := 0) (by
      intro t ht hreg
      have hb := hprefix t ht (fun s hs => sub_nonpos.mp (hreg s hs))
      have hg := image_norm_le_of_norm_deriv_right_le_deriv_boundary hp.continuousOn
        (fun r hr => (hdp r ⟨hr.1,hr.2.le.trans ht.2⟩).hasDerivWithinAt)
        (B := fun s => P s - (P 0 - ‖p 0‖)) (by simp)
        (fun s => (hP s).sub_const _) (fun r hr => hb r (Ico_subset_Icc_self hr))
        ⟨ht.1,le_rfl⟩
      linarith)
  intro t ht
  exact ⟨sub_neg.mp (hall t ht), hprefix T ⟨ht.1.trans ht.2,le_rfl⟩
    (fun s hs => (sub_neg.mp (hall s hs)).le) t ht⟩

end GNC.SecondOrderEnvelope
