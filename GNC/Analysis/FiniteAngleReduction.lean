import GNC.Analysis.FiniteAngleComparison

/-! Exact reduction of the finite-angle response basis before counting work.
The circle relation sin(theta)^2 = 2c-c^2, c=1-cos(theta), removes a redundant
quadratic response column. The identity is over real arithmetic; approximate
trigonometry and floating-point evaluation need their own error bounds.
-/
noncomputable section
namespace GNC.FiniteAngleReduction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quadratic (θ : ℝ) (S C Qss Qsc Qcc : E) : E :=
  FiniteAngleComparison.exactAngle θ S C+
    (Real.sin θ)^2 • Qss+(Real.sin θ*(1-Real.cos θ)) • Qsc+
    (1-Real.cos θ)^2 • Qcc

def reduced (s c : ℝ) (S C U V : E) : E :=
  s • (S+c • U)+c • (C+c • V)

theorem circle_relation (θ : ℝ) :
    (Real.sin θ)^2 = 2*(1-Real.cos θ)-(1-Real.cos θ)^2 := by
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Five response columns become four, without truncating the angle or
weakening the gravity approximation. The coefficient transformation is
performed once, before repeated command queries. -/
theorem quadratic_reduction (θ : ℝ) (S C Qss Qsc Qcc : E) :
    quadratic θ S C Qss Qsc Qcc =
      reduced (Real.sin θ) (1-Real.cos θ) S (C+2 • Qss) Qsc (Qcc-Qss) := by
  dsimp [quadratic, FiniteAngleComparison.exactAngle, reduced]
  rw [circle_relation]
  module

end GNC.FiniteAngleReduction
