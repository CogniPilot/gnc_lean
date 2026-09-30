import GNC.Magnus.FohVectorReduction

/-! Exact vector reduction of the candidate eighth-order exponent.
This proves the displayed finite algebra identity, not an order statement
about the actual flow and not correctness of generated machine code. -/
noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix

/-- Angular part of the displayed midpoint candidate. -/
def fohEighthAngular (F G : Vec3) : Vec3 :=
  let C := F ⨯₃ G
  F + (1/12:ℝ) • C - (1/240:ℝ) • (G ⨯₃ C) -
    (1/720:ℝ) • (F ⨯₃ (F ⨯₃ C)) +
    (1/30240:ℝ) • (F ⨯₃ (F ⨯₃ (F ⨯₃ (F ⨯₃ C)))) +
    (1/10080:ℝ) • (F ⨯₃ (F ⨯₃ (G ⨯₃ C))) -
    (1/7560:ℝ) • (C ⨯₃ (F ⨯₃ C)) +
    (1/6720:ℝ) • (G ⨯₃ (G ⨯₃ C))

set_option maxHeartbeats 8000000 in
/-- Three scalar coefficients exactly replace the nested rotational brackets. -/
theorem fohEighthAngular_reduced (F G : Vec3) :
    fohEighthAngular F G =
      (1 - fohDot G G / 240 + (fohDot F G)^2 / 30240 -
        fohDot F F * fohDot G G / 7560) • F +
      (fohDot F G / 240 + fohDot F F * fohDot F G / 10080) • G +
      (1/12 + fohDot F F / 720 + (fohDot F F)^2 / 30240 -
        fohDot G G / 6720) • (F ⨯₃ G) := by
  ext i
  fin_cases i <;>
    simp [fohEighthAngular, fohDot, cross_apply, Matrix.vecHead, Matrix.vecTail,
      smul_eq_mul] <;> ring

end GNC.Magnus
