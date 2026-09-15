import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! A phase interpolant's differential residual bounds its error without
charging the size of the known angular rate. Multiplication by the exact
unit complex phase removes that skew transport. This uses mathlib's
mean-value estimate and applies to nonconstant angular rates.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.RotationPhaseCertificate
open Complex Set

def phase (φ : ℝ) : ℂ := Complex.exp ((φ:ℂ)*I)

theorem phase_norm (φ : ℝ) : ‖phase φ‖=1 := by
  simp [phase,Complex.norm_exp]

theorem real_error_le (φ : ℝ) (p : ℂ) :
    |p.re-Real.cos φ| ≤ ‖p-phase φ‖ := by
  simpa [phase] using Complex.abs_re_le_norm (p-phase φ)

theorem imag_error_le (φ : ℝ) (p : ℂ) :
    |p.im-Real.sin φ| ≤ ‖p-phase φ‖ := by
  simpa [phase] using Complex.abs_im_le_norm (p-phase φ)

theorem phase_derivative {φ : ℝ → ℝ} {w t : ℝ}
    (hφ : HasDerivAt φ w t) :
    HasDerivAt (fun s => phase (φ s)) (phase (φ t)*((w:ℂ)*I)) t := by
  simpa [phase,mul_comm] using (hφ.ofReal_comp.mul_const I).cexp

theorem transported_derivative {φ : ℝ → ℝ} {p : ℝ → ℂ} {w t : ℝ} {v : ℂ}
    (hφ : HasDerivAt φ w t) (hp : HasDerivAt p v t) :
    HasDerivAt (fun s => phase (-φ s)*p s)
      (phase (-φ t)*(v-((w:ℂ)*I)*p t)) t := by
  convert (phase_derivative hφ.neg).mul hp using 1
  change phase (-φ t) * (v - (↑w * I) * p t) =
    (phase (-φ t) * (↑(-w) * I)) * p t + phase (-φ t) * v
  push_cast
  ring

theorem phase_inverse (φ : ℝ) : phase (-φ)*phase φ=1 := by
  rw [phase,phase,←Complex.exp_add]
  simp

theorem transported_error (φ : ℝ) (p : ℂ) :
    ‖phase (-φ)*p-1‖=‖p-phase φ‖ := by
  rw [←phase_inverse φ,←mul_sub,norm_mul,phase_norm,one_mul]

/-- On [0,T], a uniform residual budget C gives error at most C*t.
The candidate has the exact initial phase. No Magnus convergence or
state-error bound is assumed. This theorem certifies the phase only. -/
theorem error_bound (φ w : ℝ → ℝ) (p v : ℝ → ℂ) {T C : ℝ}
    (hφ : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt φ (w t) t)
    (hp : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt p (v t) t)
    (h0 : p 0=phase (φ 0))
    (hC : ∀ t ∈ Icc (0:ℝ) T, ‖v t-((w t:ℂ)*I)*p t‖≤C)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) : ‖p t-phase (φ t)‖≤C*t := by
  have hd := fun s hs =>
    (transported_derivative (hφ s hs) (hp s hs)).hasDerivWithinAt (s := Icc (0:ℝ) T)
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun s hs => by
      rw [norm_mul,phase_norm,one_mul]
      exact hC s (Ico_subset_Icc_self hs)) t ht
  simpa only [h0,phase_inverse,transported_error,sub_zero] using hb

section Synthesis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translate a complex phase error into an error in a vector forcing term.
The coefficient vectors can be evaluated separately at each time. -/
theorem synthesis_error (a b : E) (p q : ℂ) :
    ‖(p.re • a+p.im • b)-(q.re • a+q.im • b)‖ ≤
      ‖p-q‖*(‖a‖+‖b‖) := by
  have h : (p.re • a+p.im • b)-(q.re • a+q.im • b) =
      (p-q).re • a+(p-q).im • b := by
    simp only [sub_re,sub_im]
    module
  rw [h]
  calc
    _ ≤ ‖(p-q).re • a‖+‖(p-q).im • b‖ := norm_add_le _ _
    _ = |(p-q).re| * ‖a‖+|(p-q).im| * ‖b‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ‖p-q‖*‖a‖+‖p-q‖*‖b‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg a))
      (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) (norm_nonneg b))
    _ = _ := by ring

/-- The phase errors for harmonics one and two contribute additively.
No bound on the known angular rate multiplies these forcing coefficients. -/
theorem two_harmonic_error (a b c d : E) (φ : ℝ) (p q : ℂ) :
    ‖(p.re • a+p.im • b)+(q.re • c+q.im • d)-
      ((Real.cos φ • a+Real.sin φ • b)+
       (Real.cos (2*φ) • c+Real.sin (2*φ) • d))‖ ≤
      ‖p-phase φ‖*(‖a‖+‖b‖)+‖q-phase (2*φ)‖*(‖c‖+‖d‖) := by
  have h₁ := synthesis_error a b p (phase φ)
  have h₂ := synthesis_error c d q (phase (2*φ))
  simp only [phase,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im] at h₁ h₂ ⊢
  have ht := (norm_add_le _ _).trans (add_le_add h₁ h₂)
  convert ht using 1
  congr 1
  module

end Synthesis

end GNC.RotationPhaseCertificate
