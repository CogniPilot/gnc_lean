import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module

/-! Comparison of exact trigonometric forcing with a quadratic parameter
approximation. All bounds and the angle are symbolic. No orbital constants,
numerical tolerance, or coordinate-specific advantage is assumed. -/
noncomputable section
namespace GNC.FiniteAngleComparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def exactAngle (θ : ℝ) (S C : E) : E := Real.sin θ • S+(1-Real.cos θ) • C
def taylorTwo (θ : ℝ) (S C Q : E) : E := θ • S+θ^2 • ((1/2:ℝ) • C+Q)

/-- The comparator includes an arbitrary quadratic physical correction Q.
In orbital dynamics this is the gravity-Hessian response. -/
theorem error_lower (θ : ℝ) (p S C Q : E) :
    |θ-Real.sin θ| * ‖S‖ - |1-Real.cos θ-θ^2/2| * ‖C‖ -
      θ^2*‖Q‖ - ‖p-exactAngle θ S C‖ ≤ ‖p-taylorTwo θ S C Q‖ := by
  have he : (θ-Real.sin θ) • S =
      (p-exactAngle θ S C)+((1-Real.cos θ)-θ^2/2) • C-
        θ^2 • Q-(p-taylorTwo θ S C Q) := by
    dsimp [exactAngle,taylorTwo]
    module
  have hn := norm_sub_le
    ((p-exactAngle θ S C)+((1-Real.cos θ)-θ^2/2) • C-θ^2 • Q)
    (p-taylorTwo θ S C Q)
  have hn2 := norm_sub_le ((p-exactAngle θ S C)+((1-Real.cos θ)-θ^2/2) • C) (θ^2 • Q)
  have hn3 := norm_add_le (p-exactAngle θ S C) (((1-Real.cos θ)-θ^2/2) • C)
  have hleft := congrArg norm he
  simp only [norm_smul,Real.norm_eq_abs] at hleft
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg θ)] at hn2 hn3
  linarith

/-- An upper certificate for the same truncated predictor. -/
theorem error_upper (θ : ℝ) (p S C Q : E) :
    ‖p-taylorTwo θ S C Q‖ ≤ ‖p-exactAngle θ S C‖ +
      |θ-Real.sin θ| * ‖S‖ + |1-Real.cos θ-θ^2/2| * ‖C‖ + θ^2*‖Q‖ := by
  have he : p-taylorTwo θ S C Q =
      (p-exactAngle θ S C)+(Real.sin θ-θ) • S+
        ((1-Real.cos θ)-θ^2/2) • C-θ^2 • Q := by
    dsimp [exactAngle,taylorTwo]
    module
  have h1 := norm_sub_le ((p-exactAngle θ S C)+(Real.sin θ-θ) • S+
    ((1-Real.cos θ)-θ^2/2) • C) (θ^2 • Q)
  have h2 := norm_add_le ((p-exactAngle θ S C)+(Real.sin θ-θ) • S)
    (((1-Real.cos θ)-θ^2/2) • C)
  have h3 := norm_add_le (p-exactAngle θ S C) ((Real.sin θ-θ) • S)
  rw [he]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg θ),
    abs_sub_comm (Real.sin θ) θ] at h1 h2 h3
  linarith

/-- A sufficient condition comparing actual errors, rather than just upper
bounds. A ratio k>1 gives a strict multiplicative accuracy improvement. -/
theorem strict_advantage (θ : ℝ) (p S C Q : E) {ε k : ℝ}
    (hk : 0 ≤ k) (hp : ‖p-exactAngle θ S C‖ ≤ ε)
    (hgap : (k+1)*ε < |θ-Real.sin θ| * ‖S‖ -
      |1-Real.cos θ-θ^2/2| * ‖C‖ - θ^2*‖Q‖) :
    k*‖p-exactAngle θ S C‖ < ‖p-taylorTwo θ S C Q‖ := by
  have hl := error_lower θ p S C Q
  have hm := mul_le_mul_of_nonneg_left hp hk
  nlinarith

/-- The finite-angle family also supplies its pointing Jacobian directly. -/
theorem pointing_derivative (θ : ℝ) (S C : E) :
    HasDerivAt (fun a => exactAngle a S C)
      (Real.cos θ • S+Real.sin θ • C) θ := by
  convert ((Real.hasDerivAt_sin θ).smul_const S).add
    (((hasDerivAt_const θ (1:ℝ)).sub (Real.hasDerivAt_cos θ)).smul_const C) using 1
  simp

/-- A shared value/Jacobian expression. Half-angle evaluation avoids the
subtraction 1-cos(theta) in the value. This theorem is over real arithmetic. -/
def valueDerivative (θ : ℝ) (S C : E) : E × E :=
  let s := Real.sin θ
  let c := 2*(Real.sin (θ/2))^2
  (s • S+c • C,(1-c) • S+s • C)

theorem valueDerivative_correct (θ : ℝ) (S C : E) :
    (valueDerivative θ S C).1 = exactAngle θ S C ∧
      HasDerivAt (fun a => exactAngle a S C) (valueDerivative θ S C).2 θ := by
  have hc : 2*(Real.sin (θ/2))^2 = 1-Real.cos θ := by
    have h := Real.cos_two_mul (θ/2)
    have ht : 2*(θ/2) = θ := by ring
    rw [ht] at h
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  constructor
  · simp [valueDerivative,exactAngle,hc]
  · simpa [valueDerivative,hc] using pointing_derivative θ S C

end GNC.FiniteAngleComparison
