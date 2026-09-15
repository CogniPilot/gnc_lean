import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Retain a known reference fundamental flow exactly and propagate only
the remaining generator. This is the integrating-factor identity underlying
the Kepler/TH-YA specialization of the orbital propagator. It does not assert
that a particular numerical evaluation of the reference flow is certified.
-/
noncomputable section
namespace GNC.ReferenceInteraction
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def coefficient (F : Aˣ) (D : A) : A := (F⁻¹).val*D*F.val

theorem cancel (F : Aˣ) (D : A) : F.val*coefficient F D = D*F.val := by
  simp [coefficient,← mul_assoc]

/-- A numerical baseline has its own differential defect `H`. Retaining
it gives the full product defect `H * U + F * E`; baseline error is not
silently charged only to the correction integrator. -/
theorem reconstruct_inexact_defect {F : ℝ → Aˣ} {U : ℝ → A}
    {B D H E : A} {t : ℝ}
    (hF : HasDerivAt (fun s => (F s).val) (B*(F t).val+H) t)
    (hU : HasDerivAt U (coefficient (F t) D*U t+E) t) :
    HasDerivAt (fun s => (F s).val*U s)
      ((B+D)*((F t).val*U t)+(H*U t+(F t).val*E)) t := by
  convert hF.mul hU using 1
  rw [mul_add (F t).val,← mul_assoc (F t).val (coefficient (F t) D) (U t),cancel]
  noncomm_ring

theorem inexact_defect_norm (F : Aˣ) (U H E : A) :
    ‖H*U+F.val*E‖ ≤ ‖H‖*‖U‖+‖F.val‖*‖E‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-- The residual's physical defect is transported by the exact baseline;
there is no new truncation of the baseline generator. -/
theorem reconstruct_defect {F : ℝ → Aˣ} {U : ℝ → A} {B D E : A} {t : ℝ}
    (hF : HasDerivAt (fun s => (F s).val) (B*(F t).val) t)
    (hU : HasDerivAt U (coefficient (F t) D*U t+E) t) :
    HasDerivAt (fun s => (F s).val*U s)
      ((B+D)*((F t).val*U t)+(F t).val*E) t := by
  convert hF.mul hU using 1
  rw [mul_add,← mul_assoc (F t).val (coefficient (F t) D) (U t),cancel]
  noncomm_ring

theorem reconstruct_derivative {F : ℝ → Aˣ} {U : ℝ → A} {B D : A} {t : ℝ}
    (hF : HasDerivAt (fun s => (F s).val) (B*(F t).val) t)
    (hU : HasDerivAt U (coefficient (F t) D*U t) t) :
    HasDerivAt (fun s => (F s).val*U s) ((B+D)*((F t).val*U t)) t := by
  simpa using reconstruct_defect hF (show HasDerivAt U (coefficient (F t) D*U t+0) t by simpa using hU)

theorem defect_norm (F : Aˣ) (E : A) : ‖F.val*E‖ ≤ ‖F.val‖*‖E‖ := norm_mul_le _ _

theorem initial (F : ℝ → Aˣ) (U : ℝ → A) (hF : F 0 = 1) (hU : U 0 = 1) :
    (F 0).val*U 0 = 1 := by simp [hF,hU]

/-- If the perturbation vanishes, the generalized construction is exactly
the supplied reference fundamental flow. In particular it need not
approximate Kepler transport with a finite-step Magnus formula. -/
theorem zero_perturbation (F : ℝ → Aˣ) (U : ℝ → A)
    (hU : ∀ t, HasDerivAt U (coefficient (F t) 0*U t) t) (h0 : U 0 = 1) :
    ∀ t, (F t).val*U t = (F t).val := by
  have hd (t : ℝ) : HasDerivAt U 0 t := by simpa [coefficient] using hU t
  intro t
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp [h,h0]

end GNC.ReferenceInteraction
