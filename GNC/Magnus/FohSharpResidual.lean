import GNC.Magnus.ResidualBound

/-! Exact rotational degree-five residual: orthogonality removes the triangle
inequality and retains the angle between rate and slope. This is a finite
coefficient identity, not an assertion about an unbounded Magnus tail. -/
noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix

def fohRotationalResidual (w s : Vec3) : Vec3 :=
  -(1/240:ℝ) • (s ⨯₃ (w ⨯₃ s)) -
  (1/720:ℝ) • (w ⨯₃ (w ⨯₃ (w ⨯₃ s)))

/-- The two rotational residual terms are orthogonal. -/
theorem foh_rotational_residual_sq (w s : Vec3) :
    enorm (fohRotationalResidual w s)^2 =
      enorm (w ⨯₃ s)^2 * (enorm s^2 / 240^2 + enorm w^4 / 720^2) := by
  simp only [enorm_sq, show enorm w ^ 4 = lengthSq w ^ 2 by rw [← enorm_sq]; ring]
  simp [fohRotationalResidual, lengthSq, cross_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Sharp coefficient norm, including the zero or parallel cases. -/
theorem foh_rotational_residual_exact (w s : Vec3) :
    enorm (fohRotationalResidual w s) =
      enorm (w ⨯₃ s) * Real.sqrt (enorm s^2 / 240^2 + enorm w^4 / 720^2) := by
  have hs := foh_rotational_residual_sq w s
  have hp : 0 ≤ enorm s^2 / 240^2 + enorm w^4 / 720^2 := by positivity
  have hr := Real.sq_sqrt hp
  have hn := enorm_nonneg (fohRotationalResidual w s)
  have hc := enorm_nonneg (w ⨯₃ s)
  have hq := Real.sqrt_nonneg (enorm s^2 / 240^2 + enorm w^4 / 720^2)
  have he : enorm (fohRotationalResidual w s)^2 =
      (enorm (w ⨯₃ s) * Real.sqrt (enorm s^2 / 240^2 + enorm w^4 / 720^2))^2 := by
    rw [mul_pow, hr]
    exact hs
  nlinarith [mul_nonneg hc hq]

/-- Rigorous improvement over the previous triangle bound. -/
theorem foh_rotational_residual_sharp_le (w s : Vec3) :
    enorm (fohRotationalResidual w s) ≤
      enorm (w ⨯₃ s) * (enorm s / 240 + enorm w^2 / 720) := by
  rw [foh_rotational_residual_exact]
  apply mul_le_mul_of_nonneg_left _ (enorm_nonneg _)
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact add_nonneg (div_nonneg (enorm_nonneg s) (by norm_num)) (by positivity)
  · nlinarith [enorm_nonneg s, sq_nonneg (enorm w)]

end GNC.Magnus
