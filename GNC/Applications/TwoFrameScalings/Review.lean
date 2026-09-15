import GNC.Lie.TwoFrame
import GNC.Lie.AffineExponential
import GNC.Lie.SimilarityExponential
import GNC.Estimation.NoiseCoordinates

/-! Review of Chauchat, Barrau and Bonnabel, HAL hal-04691569v1.
The raw printed quotients omit their simultaneous-zero extension. This is
not a refutation of the corrected exponential with that extension supplied. -/
noncomputable section
open Matrix NormedSpace
open scoped Matrix.Norms.Operator
namespace GNC.Applications.TwoFrameScalings

def printedAlpha (s θ : ℝ) : ℝ :=
  (s*(Real.exp s*Real.cos θ-1)+Real.exp s*θ*Real.sin θ)/(s^2+θ^2)
def printedBeta (s θ : ℝ) : ℝ :=
  (θ*(1-Real.exp s*Real.cos θ)+Real.exp s*s*Real.sin θ)/(s^2+θ^2)

theorem printed_coefficients_agree (s θ : ℝ) :
    printedAlpha s θ = GNC.SimilarityExponential.alpha s θ 1 ∧
    printedBeta s θ = GNC.SimilarityExponential.beta s θ 1 := by
  constructor <;>
    simp [printedAlpha, printedBeta, GNC.SimilarityExponential.alpha,
      GNC.SimilarityExponential.beta] <;> ring

theorem printed_coefficients_at_zero : printedAlpha 0 0 = 0 ∧ printedBeta 0 0 = 0 := by
  simp [printedAlpha, printedBeta]

def translation : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => if i = 0 then 1 else 0
def printedV (s θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  printedAlpha s θ • 1+printedBeta s θ • !![0,-1;1,0]

theorem printedV_at_zero : printedV 0 0 = 0 := by
  simp [printedV, printedAlpha, printedBeta]

/-- Under Lean's totalized division, the unextended quotients erase a
nonzero pure translation; ordinary mathematical division leaves them undefined. -/
theorem unextended_exponential_fails :
    exp (GNC.Preintegration.block (0 : Matrix (Fin 2) (Fin 2) ℝ) translation 0) ≠
      fromBlocks 1 (printedV 0 0*translation) 0 1 := by
  rw [GNC.AffineExponential.pure_translation, printedV_at_zero, Matrix.zero_mul]
  intro h
  have he := congrArg (fun A => A (Sum.inl 0) (Sum.inr 0)) h
  norm_num [translation] at he

/-- The correct everywhere-defined translation kernel equals I at the
missing parameter value, as a theorem about an actual matrix integral. -/
theorem corrected_kernel_at_zero :
    GNC.AffineExponential.primitive (0 : Matrix (Fin 2) (Fin 2) ℝ) 1 = 1 := by
  simp [GNC.AffineExponential.primitive_zero_generator]

end GNC.Applications.TwoFrameScalings
