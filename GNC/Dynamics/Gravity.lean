import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Checked portions of Lemma 3 and Theorem 1. The operator lemmas below are
conditional on their displayed bounds. They do NOT establish the physical
gravity Hessian, the integral Taylor formula, or the SO(3) Jacobian norm.
-/
noncomputable section
namespace GNC
namespace Gravity

/-- The scalar factor in the squared Hessian norm, equation (20). -/
theorem hessian_factor_bound (c : ℝ) (hc : c ^ 2 ≤ 1) :
    5 * c ^ 4 - 2 * c ^ 2 + 1 ≤ 4 := by
  have h : 0 ≤ (1 - c^2) * (5*c^2 + 3) :=
    mul_nonneg (sub_nonneg.mpr hc) (by positivity)
  nlinarith

/-- The radial direction attains the scalar maximum. -/
theorem hessian_factor_radial : 5 * (1 : ℝ)^4 - 2 * 1^2 + 1 = 4 := by norm_num

/-- The closed form in (18). -/
def remainderBound (μ r d : ℝ) : ℝ := μ*d^2*(3*r - 2*d)/(r^3*(r-d)^2)

theorem remainderBound_nonneg (μ r d : ℝ) (hμ : 0 ≤ μ) (hd : 0 ≤ d) (hdr : d < r) :
    0 ≤ remainderBound μ r d := by
  unfold remainderBound
  have hr : 0 < r := lt_of_le_of_lt hd hdr
  have hrd : 0 < r - d := sub_pos.mpr hdr
  have hn : 0 < 3*r - 2*d := by linarith
  positivity

/-- Inward radial displacement attains the bound exactly, with no series
approximation. This also checks the rational expression in (21). -/
theorem radial_remainder_exact (μ r d : ℝ) (hr : r ≠ 0) (hrd : r-d ≠ 0) :
    μ/(r-d)^2 - μ/r^2 - 2*μ*d/r^3 = remainderBound μ r d := by
  unfold remainderBound
  field_simp
  ring

section Operators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The decomposition of the transformed velocity gravity block, (22)–(24). -/
theorem decomposition (B G J : E →L[ℝ] E) (p f : E) :
    B (G (J p) + f) = G p + (B (G (J p)) - G p) + B f := by
  rw [map_add]; abel

/-- Equation (29) before expanding the Jacobian polynomial. -/
theorem commutator_identity (B G J : E →L[ℝ] E) (hBJ : B * J = 1) :
    B * G * J - G = B * (G * J - J * G) := by
  rw [mul_sub, ← mul_assoc, ← mul_assoc, hBJ, one_mul]

/-- Equation (26) follows from the separately required Lemmas 2 and 3. -/
theorem transported_remainder_bound (B : E →L[ℝ] E) (f : E) (k b : ℝ)
    (hk : 0 ≤ k) (hB : ‖B‖ ≤ k) (hf : ‖f‖ ≤ b) : ‖B f‖ ≤ k*b := by
  calc
    ‖B f‖ ≤ ‖B‖ * ‖f‖ := B.le_opNorm f
    _ ≤ k * b := mul_le_mul hB hf (norm_nonneg _) hk

/-- The triangle/submultiplicativity step (31), with explicit hypotheses. -/
theorem attitude_bound_of_commutators (B C₁ C₂ : E →L[ℝ] E) (p : E)
    (k a b c₁ c₂ : ℝ) (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ‖B‖ ≤ k) (hC₁ : ‖C₁‖ ≤ c₁) (hC₂ : ‖C₂‖ ≤ c₂) :
    ‖B (a • C₁ p + b • C₂ p)‖ ≤ k * (a*c₁ + b*c₂) * ‖p‖ := by
  have h₁ : ‖a • C₁ p‖ ≤ a*c₁*‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      ((C₁.le_opNorm p).trans (mul_le_mul_of_nonneg_right hC₁ (norm_nonneg _))) ha
  have h₂ : ‖b • C₂ p‖ ≤ b*c₂*‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      ((C₂.le_opNorm p).trans (mul_le_mul_of_nonneg_right hC₂ (norm_nonneg _))) hb
  calc
    ‖B (a • C₁ p + b • C₂ p)‖ ≤ k * (a*c₁*‖p‖ + b*c₂*‖p‖) :=
      transported_remainder_bound B _ k _ hk hB ((norm_add_le _ _).trans (add_le_add h₁ h₂))
    _ = _ := by ring

end Operators
end Gravity
end GNC
