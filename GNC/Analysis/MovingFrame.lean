import GNC.Analysis.ForcedResponse

/-! Exact error transport in a moving frame. In particular, an SE₂(3)
translation column must retain the angular frame-rate term. -/
noncomputable section
namespace GNC.MovingFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
abbrev End := E →L[ℝ] E

theorem derivative (S : ℝ → (End (E := E))ˣ) (W : ℝ → End (E := E))
    (hS : ∀ t, HasDerivAt (fun s => (S s).val) (W t*(S t).val) t)
    {x : ℝ → E} {A : End (E := E)} {f : E} {t : ℝ}
    (hx : HasDerivAt x (A (x t)+f) t) :
    HasDerivAt (fun s => ((S s)⁻¹).val (x s))
      ((((S t)⁻¹).val*(A-W t)*(S t).val) (((S t)⁻¹).val (x t))+
        ((S t)⁻¹).val f) t := by
  convert (ForcedResponse.inverse_derivative S W hS t).clm_apply hx using 1
  simp [ContinuousLinearMap.mul_apply, map_add, map_sub, ForcedResponse.cancel]
  module

end GNC.MovingFrame
