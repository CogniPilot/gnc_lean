import GNC.Preintegration.SampleSensitivity
import GNC.Lie.Adjoint

/-! Reconstruct the initial-error transition from an extended nominal
increment, for any input history. No extra variational integration is needed.
Coordinate order is `(position, velocity, rotation)` throughout. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace GNC.Preintegration.Uncertainty

def extendedEndpoint (R : SO3) (v p : Vec3) (T : ℝ) : Mat5 :=
  splitMatrix.symm (fromBlocks R.val (columns v p) 0 !![1,T;0,1])

def endpointTransition (R : SO3) (v p : Vec3) (T : ℝ) (x : LogState) : LogState :=
  ![rotate R⁻¹ (x 0+T • x 1-p ⨯₃ x 2),
    rotate R⁻¹ (x 1-v ⨯₃ x 2), rotate R⁻¹ (x 2)]

private theorem mul_columns (R : SO3) (v p : Vec3) :
    R.val * columns v p = columns (rotate R v) (rotate R p) := by
  ext i j
  fin_cases j <;> simp [columns, rotate, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem skew_columns (q v p : Vec3) :
    skew q * columns v p = columns (q ⨯₃ v) (q ⨯₃ p) := by
  ext i j
  fin_cases j <;> fin_cases i <;>
    simp [columns, skew, Matrix.mul_apply, Fin.sum_univ_succ, crossProduct] <;> ring

private theorem columns_time (v p : Vec3) (T : ℝ) :
    columns v p * !![1,T;0,1] = columns v (T • v+p) := by
  ext i j
  fin_cases j <;> simp [columns, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem columns_add (v p w q : Vec3) :
    columns v p + columns w q = columns (v+w) (p+q) := by
  ext i j; fin_cases j <;> rfl

/-- Faithful matrix intertwining proves all nine coordinate blocks,
including the signs of the velocity/position attitude cross terms. -/
theorem endpointTransition_intertwine (R : SO3) (v p : Vec3) (T : ℝ) (x : LogState) :
    extendedEndpoint R v p T * hat (endpointTransition R v p T x) =
      hat x * extendedEndpoint R v p T := by
  apply splitMatrix.injective
  simp only [map_mul, extendedEndpoint, AlgEquiv.apply_symm_apply, split_hat,
    Preintegration.block, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero]
  rw [mul_columns, skew_columns, columns_time, columns_add]
  have hr := skew_rotate R (rotate R⁻¹ (x 2))
  simp only [← rotate_mul, mul_inv_cancel, rotate_one] at hr
  simp only [endpointTransition, Matrix.cons_val, ← rotate_mul, mul_inv_cancel, rotate_one]
  rw [← hr]
  congr 1
  · congr 1 <;> simp only [sub_eq_add_neg] <;> rw [cross_anticomm] <;> module

/-- The explicit endpoint formula equals the actual conjugation transition.
The nominal increment may come from ZOH, FOH, or any other input history. -/
theorem initialTransition_endpoint (U : ℝ → Mat5ˣ) (R : SO3) (v p : Vec3)
    (T : ℝ) (hU : (U T).val = extendedEndpoint R v p T) (x : LogState) :
    initialTransition U (hat x) T = hat (endpointTransition R v p T x) := by
  have h := endpointTransition_intertwine R v p T x
  rw [← hU] at h
  have hh := congrArg (fun Z => ((U T)⁻¹).val*Z) h
  simpa only [← mul_assoc, Units.inv_mul, one_mul, initialTransition] using hh.symm

end GNC.Preintegration.Uncertainty
