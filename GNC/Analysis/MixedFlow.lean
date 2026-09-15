import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-! The matrix initial-value theorem underlying the preintegration paper's
Lemma 2 and Theorem 1. Matrices M and N need not belong to a Lie algebra. -/
noncomputable section
namespace GNC.MixedInvariant
open NormedSpace

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def flow (M N X₀ : A) (t : ℝ) : A := exp (t • M) * X₀ * exp (t • N)

omit [CompleteSpace A] in
theorem flow_initial (M N X₀ : A) : flow M N X₀ 0 = X₀ := by simp [flow]

theorem exp_cancel (x : A) : exp x * exp (-x) = 1 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  rw [← exp_add_of_commute (Commute.refl x).neg_right, add_neg_cancel, exp_zero]

theorem exp_cancel' (x : A) : exp (-x) * exp x = 1 := by
  simpa using exp_cancel (-x)

theorem flow_derivative (M N X₀ : A) (t : ℝ) :
    HasDerivAt (flow M N X₀) (M * flow M N X₀ t + flow M N X₀ t * N) t := by
  convert ((hasDerivAt_exp_smul_const' M t).mul_const X₀).mul
    (hasDerivAt_exp_smul_const N t) using 1
  simp only [flow]; noncomm_ring

theorem flow_unique (M N X₀ : A) (F : ℝ → A)
    (hF : ∀ t, HasDerivAt F (M * F t + F t * N) t) (h₀ : F 0 = X₀) :
    F = flow M N X₀ := by
  let H : ℝ → A := fun t => exp ((-t) • M) * F t * exp ((-t) • N)
  have hd : ∀ t, HasDerivAt H 0 t := by
    intro t
    have hL := (hasDerivAt_exp_smul_const M (-t)).scomp t (hasDerivAt_id t).neg
    have hR := (hasDerivAt_exp_smul_const' N (-t)).scomp t (hasDerivAt_id t).neg
    convert (hL.mul (hF t)).mul hR using 1
    simp only [Function.comp_apply, Pi.mul_apply, neg_one_smul]
    noncomm_ring
  have hc (t : ℝ) : H t = X₀ := by
    have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa [H, h₀] using he
  ext t
  have he := congrArg (fun Z : A => exp (t • M) * Z * exp (t • N)) (hc t)
  calc
    F t = (exp (t • M) * exp (-(t • M))) * F t *
        (exp (-(t • N)) * exp (t • N)) := by rw [exp_cancel, exp_cancel']; simp
    _ = exp (t • M) * H t * exp (t • N) := by dsimp [H]; rw [neg_smul, neg_smul]; noncomm_ring
    _ = flow M N X₀ t := he

end Algebra
end GNC.MixedInvariant
