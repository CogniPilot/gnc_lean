import GNC.Lie.Vector3
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Euclidean geometry of the paper's three-component column vectors. -/
noncomputable section
open Matrix
open scoped Matrix
namespace GNC

/-- The genuine Euclidean norm, via mathlib's L² space. -/
def enorm (v : Vec3) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖

theorem enorm_nonneg (v : Vec3) : 0 ≤ enorm v := norm_nonneg _

theorem enorm_sq (v : Vec3) : enorm v ^ 2 = lengthSq v := by
  rw [enorm, EuclideanSpace.real_norm_sq_eq]
  simp [lengthSq, Fin.sum_univ_succ, add_assoc]

theorem dot_self_lengthSq (v : Vec3) : v ⬝ᵥ v = lengthSq v := by
  simp [dotProduct, Fin.sum_univ_succ, lengthSq]; ring

theorem lengthSq_nonneg (v : Vec3) : 0 ≤ lengthSq v := by
  rw [← enorm_sq]; positivity

theorem enorm_eq_zero_iff (v : Vec3) : enorm v = 0 ↔ v = 0 := by
  rw [← lengthSq_eq_zero_iff, ← enorm_sq, sq_eq_zero_iff]

theorem enorm_add_le (u v : Vec3) : enorm (u + v) ≤ enorm u + enorm v :=
  norm_add_le _ _

theorem enorm_smul (a : ℝ) (v : Vec3) : enorm (a • v) = |a| * enorm v :=
  norm_smul a (WithLp.toLp 2 v)

theorem enorm_neg (v : Vec3) : enorm (-v) = enorm v := norm_neg _

theorem norm_le_of_sq_le {u v : Vec3} {c : ℝ} (hc : 0 ≤ c)
    (h : lengthSq u ≤ c^2 * lengthSq v) : enorm u ≤ c * enorm v := by
  rw [← enorm_sq, ← enorm_sq] at h
  have hh : 0 ≤ c * enorm v := mul_nonneg hc (enorm_nonneg v)
  nlinarith [enorm_nonneg u, enorm_nonneg v, sq_nonneg (enorm u - c * enorm v)]

theorem rotate_lengthSq (R : SO3) (v : Vec3) : lengthSq (rotate R v) = lengthSq v := by
  rw [← dot_self_lengthSq, ← dot_self_lengthSq]
  change (R.val *ᵥ v) ⬝ᵥ (R.val *ᵥ v) = _
  rw [dotProduct_mulVec, vecMul_mulVec]
  have hR : R.valᵀ * R.val = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp R.property.1
  rw [hR]
  simp

theorem rotate_enorm (R : SO3) (v : Vec3) : enorm (rotate R v) = enorm v := by
  have h := rotate_lengthSq R v
  rw [← enorm_sq, ← enorm_sq] at h
  nlinarith [enorm_nonneg (rotate R v), enorm_nonneg v]

/-- The standard cross-product matrix. -/
def skew (v : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,-v 2,v 1; v 2,0,-v 0; -v 1,v 0,0]

theorem skew_mulVec (u v : Vec3) : skew u *ᵥ v = u ⨯₃ v := by
  ext i; fin_cases i <;> simp [skew, cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The only matrix-specific calculation needed to apply Cayley–Hamilton. -/
theorem skew_charpoly (v : Vec3) :
    (skew v).charpoly = Polynomial.X^3 + Polynomial.C (lengthSq v)*Polynomial.X := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three, skew,
    Matrix.scalar, Matrix.diagonal, lengthSq, map_add, map_pow]
  ring

/-- Specialize mathlib's Cayley–Hamilton theorem to the cross-product matrix. -/
theorem skew_cube (v : Vec3) : skew v ^ 3 = -(enorm v ^ 2) • skew v := by
  have h := Matrix.aeval_self_charpoly (skew v)
  rw [skew_charpoly] at h
  simp only [map_add, map_pow, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul] at h
  rw [enorm_sq, neg_smul]
  exact eq_neg_of_add_eq_zero_left h

theorem skew_transpose (v : Vec3) : (skew v)ᵀ = -skew v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew]

theorem skew_zero : skew 0 = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [skew]

theorem skew_smul (a : ℝ) (v : Vec3) : skew (a • v) = a • skew v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [skew]

theorem cross_lengthSq_le (u v : Vec3) : lengthSq (u ⨯₃ v) ≤ lengthSq u * lengthSq v := by
  rw [← dot_self_lengthSq, cross_dot_cross, dotProduct_comm v u]
  simp only [dot_self_lengthSq]
  nlinarith [sq_nonneg (u ⬝ᵥ v)]

theorem cross_enorm_le (u v : Vec3) : enorm (u ⨯₃ v) ≤ enorm u * enorm v := by
  apply norm_le_of_sq_le (enorm_nonneg u)
  rw [enorm_sq]
  exact cross_lengthSq_le u v

/-- A symmetric rank-two map on two orthogonal directions. -/
theorem orthogonal_pair_bound (r w v : Vec3) (hr : r ⬝ᵥ r = 1) (hrw : r ⬝ᵥ w = 0) :
    enorm ((w ⬝ᵥ v) • r + (r ⬝ᵥ v) • w) ≤ enorm w * enorm v := by
  apply norm_le_of_sq_le (enorm_nonneg w)
  have he : lengthSq ((w ⬝ᵥ v) • r + (r ⬝ᵥ v) • w) =
      lengthSq ((r ⨯₃ w) ⨯₃ v) := by
    rw [cross_cross_eq_smul_sub_smul]
    simp only [← dot_self_lengthSq, add_dotProduct, dotProduct_add, sub_dotProduct,
      dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm w r, hrw]
    ring
  rw [he, enorm_sq]
  have hcw : lengthSq (r ⨯₃ w) = lengthSq w := by
    rw [← dot_self_lengthSq, cross_dot_cross, hr, hrw, one_mul, zero_mul,
      sub_zero, dot_self_lengthSq]
  simpa [hcw] using cross_lengthSq_le (r ⨯₃ w) v

namespace Axis

def axial (k v : Vec3) : Vec3 := (k ⬝ᵥ v) • k
def transverse (k v : Vec3) : Vec3 := v - axial k v

theorem cross_sq (k v : Vec3) (hk : k ⬝ᵥ k = 1) :
    k ⨯₃ (k ⨯₃ v) = axial k v - v := by
  rw [cross_cross_eq_smul_sub_smul', hk, one_smul]; rfl

theorem cross_axial (k v : Vec3) : k ⨯₃ axial k v = 0 := by
  simp [axial]

theorem cross_transverse (k v : Vec3) : k ⨯₃ transverse k v = k ⨯₃ v := by
  simp [transverse, cross_axial]

theorem dot_transverse (k v : Vec3) (hk : k ⬝ᵥ k = 1) :
    k ⬝ᵥ transverse k v = 0 := by simp [transverse, axial, hk]

theorem transverse_sq (k v : Vec3) (hk : k ⬝ᵥ k = 1) :
    lengthSq (transverse k v) = lengthSq v - (k ⬝ᵥ v)^2 := by
  simp only [← dot_self_lengthSq, transverse, axial, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hk]
  rw [dotProduct_comm v k]; ring

theorem dot_sq_le (k v : Vec3) (hk : k ⬝ᵥ k = 1) :
    (k ⬝ᵥ v)^2 ≤ lengthSq v := by
  have h := lengthSq_nonneg (transverse k v)
  rw [transverse_sq k v hk] at h; linarith

/-- The perpendicular plane has a complex structure given by cross product. -/
theorem cross_lengthSq (k v : Vec3) (hk : k ⬝ᵥ k = 1) :
    lengthSq (k ⨯₃ v) = lengthSq v - (k ⬝ᵥ v)^2 := by
  rw [← dot_self_lengthSq, cross_dot_cross, hk, one_mul, dotProduct_comm v k,
    dot_self_lengthSq]; ring

/-- Orthogonal axis/plane decomposition, including rotation within the plane. -/
theorem combination_lengthSq (k v : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    lengthSq (axial k v + a • transverse k v + b • (k ⨯₃ v)) =
      (k ⬝ᵥ v)^2 + (a^2+b^2)*(lengthSq v - (k ⬝ᵥ v)^2) := by
  simp only [← dot_self_lengthSq, transverse, axial, add_dotProduct,
    dotProduct_add, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hk, dot_self_cross, dot_cross_self,
    cross_dot_cross]
  rw [dotProduct_comm v k]
  rw [dotProduct_comm (k ⨯₃ v) k, dotProduct_comm (k ⨯₃ v) v]
  simp only [dot_self_cross, dot_cross_self]
  ring

end Axis
end GNC
