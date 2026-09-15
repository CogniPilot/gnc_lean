import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

/-! Residual certificates for an approximate inverse of an invertible matrix.
Invertibility of the exact factor is explicit, for example from a proved
fundamental-flow construction. No floating-point inverse is assumed exact.
-/
noncomputable section
namespace GNC.InverseCertificate
variable {A : Type*} [NormedRing A]

theorem inverse_difference (F : Aˣ) (C : A) :
    (↑F⁻¹ : A)-C = ↑F⁻¹*(1-(F:A)*C) := by
  simp [mul_sub, ← mul_assoc]

/-- A right-inverse residual gives an a posteriori norm bound for the
actual inverse. The strict inequality is the mathematical denominator
condition, not a selected numerical accuracy allowance. -/
theorem inverse_norm_bound (F : Aˣ) (C : A) {ρ : ℝ} (hρ : ρ < 1)
    (hres : ‖1-(F:A)*C‖ ≤ ρ) :
    ‖(↑F⁻¹ : A)‖ ≤ ‖C‖/(1-ρ) := by
  have he : ‖(↑F⁻¹ : A)-C‖ ≤ ‖(↑F⁻¹ : A)‖*ρ := by
    rw [inverse_difference]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left hres (norm_nonneg _))
  have ht := norm_sub_le (↑F⁻¹-C : A) (-C)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  apply (le_div_iff₀ (sub_pos.mpr hρ)).mpr
  nlinarith

theorem inverse_error_bound (F : Aˣ) (C : A) {ρ : ℝ} (hρ : ρ < 1)
    (hres : ‖1-(F:A)*C‖ ≤ ρ) :
    ‖C-(↑F⁻¹ : A)‖ ≤ ‖C‖*ρ/(1-ρ) := by
  rw [norm_sub_rev, inverse_difference]
  have h0 : 0 ≤ ρ := (norm_nonneg _).trans hres
  calc
    _ ≤ ‖(↑F⁻¹ : A)‖*ρ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left hres (norm_nonneg _))
    _ ≤ (‖C‖/(1-ρ))*ρ :=
      mul_le_mul_of_nonneg_right (inverse_norm_bound F C hρ hres) h0
    _ = _ := by ring

/-- If the baseline factor itself is approximate, its error is charged
to the inverse residual before the inverse-error theorem is applied. -/
theorem residual_of_approximation (F reported C : A) {δ ρ boundC : ℝ}
    (hF : ‖F-reported‖ ≤ δ) (hC : ‖C‖ ≤ boundC)
    (hres : ‖1-reported*C‖ ≤ ρ) :
    ‖1-F*C‖ ≤ ρ+δ*boundC := by
  have he : 1-F*C = (1-reported*C)-(F-reported)*C := by noncomm_ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hres
    ((norm_mul_le _ _).trans (mul_le_mul hF hC (norm_nonneg _) ((norm_nonneg _).trans hF))))

/-- Separate the three sources of uncertainty in the interaction-frame
coefficient: the inverse, the physical generator correction, and the factor.
The identity needs neither commutativity nor exact numerical inversion. -/
theorem transported_difference (F C D Fhat Dhat : A) (inverseF : A) :
    C*Dhat*Fhat-inverseF*D*F =
      (C-inverseF)*Dhat*Fhat+inverseF*(Dhat-D)*Fhat+inverseF*D*(Fhat-F) := by
  noncomm_ring

theorem transported_error (F C D Fhat Dhat inverseF : A) :
    ‖C*Dhat*Fhat-inverseF*D*F‖ ≤
      ‖C-inverseF‖*‖Dhat‖*‖Fhat‖+
      ‖inverseF‖*‖Dhat-D‖*‖Fhat‖+‖inverseF‖*‖D‖*‖Fhat-F‖ := by
  rw [transported_difference]
  have triple (a b c : A) : ‖a*b*c‖ ≤ ‖a‖*‖b‖*‖c‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (triple _ _ _) (triple _ _ _))) (triple _ _ _))

end GNC.InverseCertificate
