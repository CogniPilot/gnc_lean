import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Analytic certificate behind Hessian/zonotope remainder bounds, including
Patel--Subbarao (AAS 25-863, arXiv:2601.17155), equations (13)--(15).
The Taylor formula is derived from actual derivatives on the entire segment.
The matrix bound is componentwise and must hold on that entire segment.
It certifies a map approximation, not an unvalidated discretization of an ODE.
-/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace GNC.TaylorCertificate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_remainder (f f₁ f₂ : ℝ → E)
    (h₁ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ s) s)
    (h₂ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ s) s)
    (hc : ContinuousOn f₂ (Icc (0:ℝ) 1)) :
    f 1 - f 0 - f₁ 0 = ∫ s in (0:ℝ)..1, (1-s) • f₂ s := by
  let F := fun s : ℝ => f s + (1-s) • f₁ s
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt F ((1-s) • f₂ s) s := by
    convert (h₁ s hs).add (((hasDerivAt_id s).const_sub 1).smul (h₂ s hs)) using 1
    simp only [neg_smul, one_smul, id_eq]
    module
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa using hs))
    (((continuousOn_const.sub continuousOn_id).smul hc).intervalIntegrable_of_Icc
      (by norm_num))
  dsimp [F] at hi
  simp only [sub_self, zero_smul, add_zero, sub_zero, one_smul] at hi
  rw [hi]
  abel

theorem remainder_bound (f f₁ f₂ : ℝ → E) {B : ℝ}
    (h₁ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ s) s)
    (h₂ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f₁ (f₂ s) s)
    (hc : ContinuousOn f₂ (Icc (0:ℝ) 1))
    (hB : ∀ s ∈ Icc (0:ℝ) 1, ‖f₂ s‖ ≤ B) :
    ‖f 1 - f 0 - f₁ 0‖ ≤ B/2 := by
  rw [integral_remainder f f₁ f₂ h₁ h₂ hc]
  have hb (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖(1-s) • f₂ s‖ ≤ (1-s)*B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    exact mul_le_mul_of_nonneg_left (hB s hs) (sub_nonneg.mpr hs.2)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun s hs => hb s ⟨hs.1.le,hs.2⟩)
    (((continuous_const.sub continuous_id).mul_const B).intervalIntegrable
      (μ := volume) 0 1)
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => t-t^2/2) (1-s) s := by
    convert (hasDerivAt_id s).sub (((hasDerivAt_id s).pow 2).div_const 2) using 1
    simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ uIcc (0:ℝ) 1) => hd s)
    ((continuous_const.sub continuous_id).intervalIntegrable (μ := volume) 0 1)
  rw [intervalIntegral.integral_mul_const, he] at hi
  norm_num at hi ⊢
  linarith

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The absolute Hessian quadratic form, with every cross term retained. -/
theorem quadratic_bound (H M : ι → ι → ℝ) (d γ : ι → ℝ)
    (hγ : ∀ j, 0 ≤ γ j) (hM : ∀ j k, 0 ≤ M j k)
    (hd : ∀ j, |d j| ≤ γ j) (hH : ∀ j k, |H j k| ≤ M j k) :
    |∑ j, ∑ k, d j * H j k * d k| ≤ ∑ j, ∑ k, γ j * M j k * γ k := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (hd j) (hH j k) (abs_nonneg _) (hγ j))
    (hd k) (abs_nonneg _) (mul_nonneg (hγ j) (hM j k))

omit [Fintype ι] in
/-- Bounding a zonotope displacement about any chosen expansion point. -/
theorem zonotope_displacement (c z : ι → ℝ) (g : κ → ι → ℝ) (β : κ → ℝ)
    (hβ : ∀ k, |β k| ≤ 1) (j : ι) :
    |c j + ∑ k, β k*g k j - z j| ≤ |c j-z j| + ∑ k, |g k j| := by
  have hb : |∑ k, β k*g k j| ≤ ∑ k, |g k j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right (hβ k) (abs_nonneg (g k j))
  have he : c j + ∑ k, β k*g k j - z j = (c j-z j) + ∑ k, β k*g k j := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add_right hb _)

/-- Equations (13)--(15), from actual first/second directional derivatives.
For a map g, instantiate f(s)=g(z+s*d) componentwise and supply its chain
rule proofs. A numerical Hessian at z alone is not an admissible hH. -/
theorem hessian_remainder (f f₁ : ℝ → ℝ) (H : ℝ → ι → ι → ℝ)
    (M : ι → ι → ℝ) (d γ : ι → ℝ)
    (h₁ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt f (f₁ s) s)
    (h₂ : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt f₁ (∑ j, ∑ k, d j * H s j k * d k) s)
    (hc : ContinuousOn (fun s => ∑ j, ∑ k, d j * H s j k * d k) (Icc (0:ℝ) 1))
    (hγ : ∀ j, 0 ≤ γ j) (hM : ∀ j k, 0 ≤ M j k)
    (hd : ∀ j, |d j| ≤ γ j)
    (hH : ∀ s ∈ Icc (0:ℝ) 1, ∀ j k, |H s j k| ≤ M j k) :
    |f 1-f 0-f₁ 0| ≤ (∑ j, ∑ k, γ j*M j k*γ k)/2 := by
  exact remainder_bound f f₁ _ h₁ h₂ hc
    (fun s hs => by simpa using quadratic_bound (H s) M d γ hγ hM hd (hH s hs))

end GNC.TaylorCertificate
