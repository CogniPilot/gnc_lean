import GNC.Control.LMI
import GNC.Control.PolytopicTube
import GNC.Lie.Euclidean

/-! Counterexamples and exact corrections for the supplied accepted manuscript:
Lin, Goppert, Hwang, IEEE TAC 2024, DOI 10.1109/TAC.2024.3369549.
This is not a formalization of every theorem of that paper.
-/
noncomputable section
open Matrix Real
open scoped Matrix
namespace GNC.DynamicInversionReview

/-- Equations (16) and (17) cannot be mutual inverses, regardless of the
upper blocks: the bottom-right entry of their product is -1, not 1. -/
theorem printed_inverse_sign_failure (a b c d e f p q r s t u : ℝ) :
    ( !![-a,-b,-c; -d,-e,-f; 0,0,-1] : Matrix (Fin 3) (Fin 3) ℝ) *
      !![p,q,r; s,t,u; 0,0,1] ≠ 1 := by
  intro h
  have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.cons_val] at hh
  norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hh

def printedC1 (θ : ℝ) := (1-θ^2/2-cos θ)/θ^2
def seriesC1 (θ : ℝ) := (1-cos θ)/θ^2
def printedC3 (θ : ℝ) := (θ^2/2-θ^4/24+cos θ-1)/θ^4
def seriesC3 (θ : ℝ) := (θ^2/2+cos θ-1)/θ^4

/-- Exact discrepancy from the coefficient of Omega in Appendix C's
displayed series. The identification of the whole SE(2) series is separate. -/
theorem c1_discrepancy {θ : ℝ} (hθ : θ ≠ 0) :
    printedC1 θ = seriesC1 θ-1/2 := by
  unfold printedC1 seriesC1
  field_simp
  ring

theorem c3_discrepancy {θ : ℝ} (hθ : θ ≠ 0) :
    printedC3 θ = seriesC3 θ-1/24 := by
  unfold printedC3 seriesC3
  field_simp
  ring

theorem coefficients_differ {θ : ℝ} (hθ : θ ≠ 0) :
    printedC1 θ ≠ seriesC1 θ ∧ printedC3 θ ≠ seriesC3 θ := by
  rw [c1_discrepancy hθ, c3_discrepancy hθ]
  constructor <;> intro h <;> linarith

/-- Appendix C's stated determinant has a nonzero-angle zero. Its claim
of never vanishing requires a restricted chart, not all real angles. -/
theorem determinant_claim_has_zero :
    2*π ≠ 0 ∧ -2*(cos (2*π)-1)/(2*π)^2 = 0 := by
  constructor
  · positivity
  · simp

def planarRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ,-sin θ; sin θ,cos θ]

/-- Closed endpoints of [-pi,pi] cannot give a one-to-one rotation chart. -/
theorem closed_chart_endpoints_duplicate :
    π ≠ -π ∧ planarRotation π = planarRotation (-π) := by
  constructor
  · linarith [pi_pos]
  · simp [planarRotation]

/-- Minimizing mu with no normalization of the freely scaled metric is
not an invariant measure of ellipsoid size: this set is unchanged. -/
theorem ellipsoid_scale_invariant {c : ℝ} (hc : 0 < c) (V μ δ : ℝ) :
    c*V ≤ (c*μ)*δ^2 ↔ V ≤ μ*δ^2 := by
  rw [mul_assoc, mul_le_mul_iff_right₀ hc]

end GNC.DynamicInversionReview
