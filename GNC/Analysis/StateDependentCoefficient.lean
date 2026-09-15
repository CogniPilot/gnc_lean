import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! The state-dependent coefficient representation used in nonlinear
reachability. The origin offset is explicit. This is a segmentwise calculus
identity and does not assert that the resulting system is group affine.
-/
noncomputable section
open Set MeasureTheory
namespace GNC.StateDependentCoefficient
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The integral-Jacobian formula underlying the SDC representation. The
line segment must lie in the differentiability domain; singular gravity at
the origin cannot be integrated through without a coordinate translation. -/
theorem integral_jacobian (f : E → F) (D : E → E →L[ℝ] F) (x : E)
    (hd : ∀ s ∈ Icc (0:ℝ) 1, HasFDerivAt f (D (s • x)) (s • x))
    (hc : ContinuousOn (fun s : ℝ => D (s • x) x) (Icc (0:ℝ) 1)) :
    f x = f 0 + ∫ s in (0:ℝ)..1, D (s • x) x := by
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => f (t • x)) (D (s • x) x) s := by
    exact (hd s hs).comp_hasDerivAt s (by simpa using (hasDerivAt_id s).smul_const x)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hder s (by simpa using hs)) (hc.intervalIntegrable_of_Icc (by norm_num))
  simp only [one_smul, zero_smul] at hi
  rw [hi]
  abel

theorem equilibrium_representation (f : E → F) (D : E → E →L[ℝ] F) (x : E)
    (hzero : f 0 = 0)
    (hd : ∀ s ∈ Icc (0:ℝ) 1, HasFDerivAt f (D (s • x)) (s • x))
    (hc : ContinuousOn (fun s : ℝ => D (s • x) x) (Icc (0:ℝ) 1)) :
    f x = ∫ s in (0:ℝ)..1, D (s • x) x := by
  simpa [hzero] using integral_jacobian f D x hd hc

omit [CompleteSpace F] in
/-- A coefficient representation without an offset necessarily fixes zero. -/
theorem zero_necessary (f : E → F) (A : E → E →L[ℝ] F)
    (h : ∀ x, f x = A x x) : f 0 = 0 := by simpa using h 0

end GNC.StateDependentCoefficient
