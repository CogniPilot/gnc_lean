import GNC.Analysis.FiniteAngleComparison
import Mathlib.Analysis.Normed.Operator.Basic

/-! Retaining an uncertain constant angle in a general forced linear ODE.
The generator and both forcing functions may vary arbitrarily with time.
The known trigonometric dependence is not replaced by an angle Taylor jet. -/
noncomputable section
namespace GNC.FiniteAngleResponse
open FiniteAngleComparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative (A : ℝ → E →L[ℝ] E) (f g S C : ℝ → E) (θ t : ℝ)
    (hS : HasDerivAt S (A t (S t)+f t) t)
    (hC : HasDerivAt C (A t (C t)+g t) t) :
    HasDerivAt (fun s => exactAngle θ (S s) (C s))
      (A t (exactAngle θ (S t) (C t))+exactAngle θ (f t) (g t)) t := by
  convert (hS.const_smul (Real.sin θ)).add
    (hC.const_smul (1-Real.cos θ)) using 1
  simp only [exactAngle,map_add,map_smul]
  module

theorem initial (S C : ℝ → E) (θ : ℝ) (hS : S 0 = 0) (hC : C 0 = 0) :
    exactAngle θ (S 0) (C 0) = 0 := by simp [exactAngle,hS,hC]

end GNC.FiniteAngleResponse
