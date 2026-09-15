import GNC.Lie.Adjoint

/-! Signed coordinate-axis rotations as actual special orthogonal matrices,
with their body angular velocities and the product rule. -/
noncomputable section
set_option autoImplicit false
namespace GNC.AxisRotation
open Matrix Real
open scoped Matrix Matrix.Norms.Operator

def xMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,0,0; 0,cos a,-sin a; 0,sin a,cos a]
def zMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos a,-sin a,0; sin a,cos a,0; 0,0,1]

theorem x_orthogonal (a : ℝ) : (xMatrix a).transpose*xMatrix a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMatrix, mul_apply, Fin.sum_univ_succ] <;> nlinarith [sin_sq_add_cos_sq a]
theorem z_orthogonal (a : ℝ) : (zMatrix a).transpose*zMatrix a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zMatrix, mul_apply, Fin.sum_univ_succ] <;> nlinarith [sin_sq_add_cos_sq a]
theorem x_det (a : ℝ) : (xMatrix a).det = 1 := by
  simp [xMatrix, det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith [sin_sq_add_cos_sq a]
theorem z_det (a : ℝ) : (zMatrix a).det = 1 := by
  simp [zMatrix, det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith [sin_sq_add_cos_sq a]

def xRotation (a : ℝ) : SO3 :=
  ⟨xMatrix a, (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (x_orthogonal a), x_det a⟩
def zRotation (a : ℝ) : SO3 :=
  ⟨zMatrix a, (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (z_orthogonal a), z_det a⟩

@[simp] theorem x_zero : xRotation 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [xRotation, xMatrix]
@[simp] theorem z_zero : zRotation 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [zRotation, zMatrix]

theorem x_derivative {a : ℝ → ℝ} {d t : ℝ} (ha : HasDerivAt a d t) :
    HasDerivAt (fun s => (xRotation (a s)).val)
      ((xRotation (a t)).val*skew ![d,0,0]) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [xRotation, xMatrix, skew, mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, neg_zero,
      mul_neg, neg_mul, neg_neg]
  all_goals first | simpa using (hasDerivAt_const t (0:ℝ)) |
    simpa using (hasDerivAt_const t (1:ℝ)) |
    simpa [mul_comm] using ha.cos |
    simpa [mul_comm] using ha.sin | simpa [mul_comm] using ha.sin.neg

theorem z_derivative {a : ℝ → ℝ} {d t : ℝ} (ha : HasDerivAt a d t) :
    HasDerivAt (fun s => (zRotation (a s)).val)
      ((zRotation (a t)).val*skew ![0,0,d]) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [zRotation, zMatrix, skew, mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_zero, zero_mul, one_mul, mul_one, add_zero, zero_add, neg_zero,
      mul_neg, neg_mul, neg_neg]
  all_goals first | simpa using (hasDerivAt_const t (0:ℝ)) |
    simpa using (hasDerivAt_const t (1:ℝ)) |
    simpa [mul_comm] using ha.cos |
    simpa [mul_comm] using ha.sin | simpa [mul_comm] using ha.sin.neg

theorem product_derivative {A B : ℝ → SO3} {a b : Vec3} {t : ℝ}
    (hA : HasDerivAt (fun s => (A s).val) ((A t).val*skew a) t)
    (hB : HasDerivAt (fun s => (B s).val) ((B t).val*skew b) t) :
    HasDerivAt (fun s => (A s*B s).val)
      ((A t*B t).val*skew (rotate (B t)⁻¹ a+b)) t := by
  have he := skew_rotate (B t) (rotate (B t)⁻¹ a)
  simp only [← rotate_mul, mul_inv_cancel, rotate_one] at he
  convert hA.mul hB using 1
  change (A t).val*(B t).val*skew (rotate (B t)⁻¹ a+b) = _
  rw [skew_add, Matrix.mul_add]
  simp only [Matrix.mul_assoc, ← he]

end GNC.AxisRotation
