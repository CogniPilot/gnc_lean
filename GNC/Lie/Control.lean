import GNC.Lie.SE23
import Mathlib.Analysis.Normed.Operator.Basic

/-! Algebraic parts of Theorem 3 and Proposition 2. Residual norm assembly
explicitly assumes the SO(3) diagonal and M bounds; those are not axioms.
-/
noncomputable section
open Matrix
open scoped Matrix
namespace GNC

/-- Equation (62). -/
def mismatchCorrection (ν x : LogState) : LogState := (1/2 : ℝ) • ad ν x

/-- The adjoint sign in (72) really centers the linearization at the mean. -/
theorem mean_input_ad (ν νbar x : LogState) :
    -ad ν x + mismatchCorrection (ν - νbar) x =
      -ad ((1/2 : ℝ) • (ν + νbar)) x := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ad, mismatchCorrection, cross_apply] <;> ring

theorem reference_input_ad (ν νbar x : LogState) :
    -ad ν x + mismatchCorrection (ν - νbar) x =
      -ad νbar x - mismatchCorrection (ν - νbar) x := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ad, mismatchCorrection, cross_apply] <;> ring

theorem matched_correction_zero (x : LogState) : mismatchCorrection 0 x = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mismatchCorrection, ad]

namespace Control
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The diagonal identity (67) is exact for the supplied inverse polynomial. -/
theorem diagonal_decomposition (S : E →L[ℝ] E) (c : ℝ) (z : E) :
    z - (1/2 : ℝ) • S z + c • S (S z) =
      z + (-(1/2 : ℝ)) • S z + c • S (S z) := by
  simp [sub_eq_add_neg]

/-- Assembly of all three bounds (63)–(65) from diagonal and off-diagonal
operator estimates. The displayed hypotheses are the unverified analytic inputs. -/
theorem residual_bounds (D Mp Mv : E →L[ℝ] E) (da dw : E)
    (α β p v : ℝ)
    (hD : ‖D‖ ≤ β) (hMp : ‖Mp‖ ≤ α*p) (hMv : ‖Mv‖ ≤ α*v) :
    ‖Mp dw‖ ≤ α*p*‖dw‖ ∧
    ‖D da + Mv dw‖ ≤ β*‖da‖ + α*v*‖dw‖ ∧
    ‖D dw‖ ≤ β*‖dw‖ := by
  have bound (A : E →L[ℝ] E) (z : E) (c : ℝ) (h : ‖A‖ ≤ c) :
      ‖A z‖ ≤ c*‖z‖ :=
    (A.le_opNorm z).trans (mul_le_mul_of_nonneg_right h (norm_nonneg z))
  exact ⟨bound Mp dw _ hMp,
    (norm_add_le _ _).trans (add_le_add (bound D da _ hD) (bound Mv dw _ hMv)),
    bound D dw _ hD⟩

end Control
end GNC
