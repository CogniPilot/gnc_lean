import GNC.Lie.RotationDifferential

/-! Identification of the finite SE₂(3) Jacobian with the differential of
mathlib's matrix exponential, followed by an inverse differential statement
for differentiable exponential-coordinate curves. -/
noncomputable section
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem rotationDerivative_trivialized_at (q u : Vec3) (hq : 0 < enorm q) :
    rotationDerivative q u = skew (Jacobian.leftAt q u) * (rotationExp q).val := by
  have h := rotationDerivative_trivialized (Jacobian.unitAxis q) u
    (Jacobian.unitAxis_unit q hq) (enorm q) hq
  simpa only [Jacobian.unitAxis_reconstruct q hq, Jacobian.leftAt_eq q u hq] using h

theorem Q_antisymmetric_at (q u v : Vec3) (hq : 0 < enorm q) :
    Jacobian.Q q u v - Jacobian.Q q v u = Jacobian.leftAt q u ⨯₃ Jacobian.leftAt q v := by
  have h := Jacobian.Q_antisymmetric (Jacobian.unitAxis q) u v
    (Jacobian.unitAxis_unit q hq) (enorm q) hq
  simpa only [Jacobian.unitAxis_reconstruct q hq, Jacobian.leftAt_eq q u hq,
    Jacobian.leftAt_eq q v hq] using h

def coordinateDerivative (x y : LogState) : Mat5 := splitMatrix.symm
  (fromBlocks (rotationDerivative (x 2) (y 2))
    (columns (Jacobian.leftDerivative (x 2) (y 2) (x 1) + Jacobian.leftAt (x 2) (y 1))
      (Jacobian.leftDerivative (x 2) (y 2) (x 0) + Jacobian.leftAt (x 2) (y 0))) 0 0)

theorem coordinateDerivative_trivialized (x y : LogState) (hq : 0 < enorm (x 2)) :
    coordinateDerivative x y = hat (Jacobian.blockLeft x y) * SE23.toMatrix (groupExp x) := by
  apply splitMatrix.injective
  simp only [coordinateDerivative, AlgEquiv.apply_symm_apply, map_mul, split_hat, split_group]
  simp only [Preintegration.block, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, Matrix.mul_one]
  congr 1
  · exact rotationDerivative_trivialized_at (x 2) (y 2) hq
  · have ht (v w : Vec3) :
        Jacobian.leftDerivative (x 2) (y 2) v + Jacobian.leftAt (x 2) w =
        skew (Jacobian.leftAt (x 2) (y 2)) *ᵥ Jacobian.leftAt (x 2) v +
          (Jacobian.leftAt (x 2) w + Jacobian.Q (x 2) v (y 2)) := by
      rw [← Jacobian.Q_formula _ _ _ hq, skew_mulVec, ← Q_antisymmetric_at _ _ _ hq]
      abel
    ext i j
    fin_cases j
    · exact congrFun (ht (x 1) (y 1)) i
    · exact congrFun (ht (x 0) (y 0)) i

theorem groupExp_affine_derivative (x y : LogState) (hq : 0 < enorm (x 2)) :
    HasDerivAt (fun s : ℝ => SE23.toMatrix (groupExp (x+s • y))) (coordinateDerivative x y) 0 := by
  have hr := rotationExp_derivative (x 2) (y 2) hq
  have hv := Jacobian.leftAt_curve_derivative (x 2) (y 2)
    (((hasDerivAt_id (0:ℝ)).smul_const (y 1)).const_add (x 1)) hq
  have hp := Jacobian.leftAt_curve_derivative (x 2) (y 2)
    (((hasDerivAt_id (0:ℝ)).smul_const (y 0)).const_add (x 0)) hq
  simp only [id_eq, zero_smul, add_zero, one_smul] at hv hp
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> first
    | exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hr _) _
    | exact hasDerivAt_pi.mp hv _
    | exact hasDerivAt_pi.mp hp _
    | exact hasDerivAt_const (0:ℝ) (0:ℝ)
    | exact hasDerivAt_const (0:ℝ) (1:ℝ)

/-- The full block formula is the actual derivative, rather than an
independently defined map with an assumed relationship to exp. -/
theorem matrixExp_affine_derivative (x y : LogState) (hq : 0 < enorm (x 2)) :
    HasDerivAt (fun s : ℝ => exp (hat (x+s • y)))
      (hat (Jacobian.blockLeft x y)*exp (hat x)) 0 := by
  simpa only [groupExp_toMatrix, coordinateDerivative_trivialized x y hq] using
    groupExp_affine_derivative x y hq

theorem matrixExp_differentiable (x : LogState) :
    DifferentiableAt ℝ (fun z : LogState => exp (hat z)) x := by
  have he := (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) (hat x)
    (by simp [NormedSpace.expSeries_radius_eq_top])).differentiableAt
  exact he.comp x hatLinear.toContinuousLinearMap.differentiableAt

theorem matrixExp_fderiv (x y : LogState) (hq : 0 < enorm (x 2)) :
    fderiv ℝ (fun z : LogState => exp (hat z)) x y =
      hat (Jacobian.blockLeft x y)*exp (hat x) := by
  have hp : HasDerivAt (fun s : ℝ => x+s • y) y 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const y).const_add x
  have hF : HasFDerivAt (fun z : LogState => exp (hat z))
      (fderiv ℝ (fun z : LogState => exp (hat z)) x) (x+(0:ℝ) • y) := by
    simpa using (matrixExp_differentiable x).hasFDerivAt
  have he := hF.comp_hasDerivAt 0 hp
  simpa using he.unique (matrixExp_affine_derivative x y hq)

/-- The exponential differential along any differentiable log-coordinate
curve, not just a fixed-direction line. -/
theorem matrixExp_curve_derivative {x : ℝ → LogState} {y : LogState} {t : ℝ}
    (hx : HasDerivAt x y t) (hq : 0 < enorm (x t 2)) :
    HasDerivAt (fun s => exp (hat (x s)))
      (hat (Jacobian.blockLeft (x t) y)*exp (hat (x t))) t := by
  have he := (matrixExp_differentiable (x t)).hasFDerivAt.comp_hasDerivAt t hx
  simpa only [matrixExp_fderiv (x t) y hq] using he

end GNC
