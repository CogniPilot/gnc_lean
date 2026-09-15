import GNC.Preintegration.ClosedForm
import GNC.Lie.ControlResidual
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Order.IntermediateValue

/-! The SE₂(3) coordinate exponential, proved equal to mathlib's matrix
exponential. The output is an actual element of the previously constructed
SE₂(3) group, including an actual special orthogonal rotation. -/
noncomputable section
open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GNC

theorem matrix_exp_det_pos {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : 0 < (exp A).det := by
  let f : ℝ → ℝ := fun t => (exp (t • A)).det
  have hc : Continuous f := (NormedSpace.exp_continuous.comp
    (continuous_id.smul continuous_const)).matrix_det
  have hn (t : ℝ) : f t ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (NormedSpace.isUnit_exp (t • A))).ne_zero
  by_contra h
  have hle : f 1 ≤ 0 := by simpa [f] using le_of_not_gt h
  have hz : 0 ∈ Set.Icc (f 1) (f 0) := ⟨hle, by simp [f]⟩
  obtain ⟨s,hs⟩ := intermediate_value_univ 1 0 hc hz
  exact hn s hs

theorem exp_skew_mem_SO3 (q : Vec3) : exp (skew q) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have ho : (exp (skew q))ᵀ * exp (skew q) = 1 := by
    rw [← Matrix.exp_transpose, skew_transpose, MixedInvariant.exp_cancel']
  apply Matrix.mem_specialOrthogonalGroup_iff.mpr
  refine ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr ho, ?_⟩
  have hd := congrArg Matrix.det ho
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  nlinarith [matrix_exp_det_pos (skew q)]

def rotationExp (q : Vec3) : SO3 := ⟨exp (skew q), exp_skew_mem_SO3 q⟩

def jacobianMatrix (q : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + ((1-Real.cos (enorm q))/enorm q^2) • skew q +
    ((enorm q-Real.sin (enorm q))/enorm q^3) • skew q^2

theorem jacobianMatrix_mulVec (q v : Vec3) : jacobianMatrix q *ᵥ v = Jacobian.leftAt q v := by
  simp [jacobianMatrix, Jacobian.leftAt, Matrix.add_mulVec, Matrix.smul_mulVec,
    pow_two, ← Matrix.mulVec_mulVec, skew_mulVec]

def columns (v p : Vec3) : Matrix (Fin 3) (Fin 2) ℝ := fun i => ![v i,p i]

def splitMatrix : Mat5 ≃ₐ[ℝ] Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (finSumFinEquiv (m := 3) (n := 2)).symm

theorem split_hat (x : LogState) :
    splitMatrix (hat x) = Preintegration.block (skew (x 2)) (columns (x 1) (x 0)) 0 := by
  ext (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;> rfl

theorem split_group (X : SE23) :
    splitMatrix (SE23.toMatrix X) = fromBlocks X.rot.val (columns X.vel X.pos) 0 1 := by
  ext (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;> rfl

theorem translation_is_jacobian (q : Vec3) (A : Matrix (Fin 3) (Fin 2) ℝ) :
    Preintegration.translationAll (skew q) A 0 (enorm q) 1 = jacobianMatrix q * A := by
  by_cases hq : enorm q = 0
  · have hz := (enorm_eq_zero_iff q).mp hq
    subst q
    simp [Preintegration.translationAll, jacobianMatrix, skew_zero,
      (enorm_eq_zero_iff (0:Vec3)).mpr rfl, Matrix.zero_mul]
  · simp [Preintegration.translationAll, hq, Preintegration.translation,
      Preintegration.f₁, Preintegration.f₂, Preintegration.f₃, jacobianMatrix,
      Matrix.mul_zero, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]

theorem jacobian_columns (q v p : Vec3) :
    jacobianMatrix q * columns v p = columns (Jacobian.leftAt q v) (Jacobian.leftAt q p) := by
  ext i j
  fin_cases j
  · exact congrFun (jacobianMatrix_mulVec q v) i
  · exact congrFun (jacobianMatrix_mulVec q p) i

/-- Equation (4): group exponential in the paper's (p,v,R) coordinates. -/
def groupExp (x : LogState) : SE23 :=
  ⟨rotationExp (x 2), Jacobian.leftAt (x 2) (x 1), Jacobian.leftAt (x 2) (x 0)⟩

/-- The coordinate formula is the actual matrix exponential, including zero
rotation vectors. This is not a newly postulated exponential operation. -/
theorem groupExp_toMatrix (x : LogState) : SE23.toMatrix (groupExp x) = exp (hat x) := by
  apply splitMatrix.injective
  rw [NormedSpace.map_exp splitMatrix splitMatrix.toLinearMap.continuous_of_finiteDimensional,
    split_hat]
  have hz (h : enorm (x 2) = 0) : skew (x 2) = 0 := by
    rw [(enorm_eq_zero_iff _).mp h, skew_zero]
  have he := Preintegration.exp_block_all (skew (x 2)) (columns (x 1) (x 0))
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (enorm (x 2)) 1 (skew_cube (x 2)) hz (by simp)
  simp only [one_smul, smul_zero, add_zero, translation_is_jacobian, jacobian_columns] at he
  rw [he, split_group]
  rfl

end GNC
