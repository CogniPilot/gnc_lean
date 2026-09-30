import GNC.Lie.CayleyChart
import GNC.Lie.RotationKinematics

/-! Real right-quaternion kinematics recovered as an actual SO(3) solution.
The unit constraint is proved from the ODE, and the rotation matrix is an
explicit quadratic polynomial in the four real components. -/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GNC.Magnus

def fohQuaternionMatrix (a : ℝ) (v : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (a ^ 2 - lengthSq v) • 1 + (2 : ℝ) • vecMulVec v v + (2 * a) • skew v

theorem foh_quaternion_orthogonal (a : ℝ) (v : Vec3) :
    (fohQuaternionMatrix a v).transpose * fohQuaternionMatrix a v =
      ((a ^ 2 + lengthSq v) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fohQuaternionMatrix, lengthSq, skew, mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      vecMulVec] <;> ring

theorem foh_quaternion_det (a : ℝ) (v : Vec3) :
    (fohQuaternionMatrix a v).det = (a ^ 2 + lengthSq v) ^ 3 := by
  simp [fohQuaternionMatrix, lengthSq, skew, det_fin_three, vecMulVec]
  ring

def fohQuaternionRotation (a : ℝ) (v : Vec3) (h : a ^ 2 + lengthSq v = 1) : SO3 :=
  ⟨fohQuaternionMatrix a v,
    (mem_orthogonalGroup_iff' (Fin 3) ℝ).mpr (by rw [foh_quaternion_orthogonal, h]; simp),
    by change (fohQuaternionMatrix a v).det = 1; rw [foh_quaternion_det, h]; norm_num⟩

theorem foh_quaternion_norm_constant
    (a : ℝ → ℝ) (v w : ℝ → Vec3)
    (ha : ∀ t, HasDerivAt a (-(v t ⬝ᵥ w t) / 2) t)
    (hv : ∀ t, HasDerivAt v ((1 / 2 : ℝ) • (a t • w t + v t ⨯₃ w t)) t)
    (t t₀ : ℝ) : a t ^ 2 + lengthSq (v t) = a t₀ ^ 2 + lengthSq (v t₀) := by
  have hd (t : ℝ) : HasDerivAt (fun s => a s ^ 2 + lengthSq (v s)) 0 t := by
    have hvi (i : Fin 3) := hasDerivAt_pi.mp (hv t) i
    convert (ha t).pow 2 |>.add (((hvi 0).pow 2 |>.add ((hvi 1).pow 2)).add ((hvi 2).pow 2)) using 1
    simp [dotProduct, Fin.sum_univ_succ, cross_apply,
      Matrix.vecHead, Matrix.vecTail]
    ring
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t t₀

theorem foh_quaternion_unit
    (a : ℝ → ℝ) (v w : ℝ → Vec3)
    (ha : ∀ t, HasDerivAt a (-(v t ⬝ᵥ w t) / 2) t)
    (hv : ∀ t, HasDerivAt v ((1 / 2 : ℝ) • (a t • w t + v t ⨯₃ w t)) t)
    (ha0 : a 0 = 1) (hv0 : v 0 = 0) (t : ℝ) : a t ^ 2 + lengthSq (v t) = 1 := by
  rw [foh_quaternion_norm_constant a v w ha hv t 0, ha0, hv0]
  simp [lengthSq]

theorem foh_quaternionMatrix_derivative
    {a : ℝ → ℝ} {v : ℝ → Vec3} {da : ℝ} {dv : Vec3} {t : ℝ}
    (ha : HasDerivAt a da t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => fohQuaternionMatrix (a s) (v s))
      ((2 * a t * da - (2 * v t 0 * dv 0 + 2 * v t 1 * dv 1 + 2 * v t 2 * dv 2)) • 1 +
       (2 : ℝ) • (vecMulVec dv (v t) + vecMulVec (v t) dv) +
       (2 * da) • skew (v t) + (2 * a t) • skew dv) t := by
  have hvi (i : Fin 3) := hasDerivAt_pi.mp hv i
  have hn : HasDerivAt (fun s => lengthSq (v s))
      (2 * v t 0 * dv 0 + 2 * v t 1 * dv 1 + 2 * v t 2 * dv 2) t := by
    convert ((hvi 0).pow 2 |>.add ((hvi 1).pow 2)).add ((hvi 2).pow 2) using 1
    simp
  have ho : HasDerivAt (fun s => vecMulVec (v s) (v s))
      (vecMulVec dv (v t) + vecMulVec (v t) dv) t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    exact (hvi i).mul (hvi j)
  have hs : HasDerivAt (fun s => skew (v s)) (skew dv) t :=
    Cayley.skewLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hv
  have hd := (((ha.pow 2).sub hn).smul_const (1 : Matrix (Fin 3) (Fin 3) ℝ)).add
    (ho.const_smul (2 : ℝ)) |>.add ((ha.const_mul 2).smul hs)
  convert hd using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  module

/-- The explicit quadratic quaternion map intertwines the real quaternion
ODE and the right rotation ODE, without imposing a norm hypothesis. -/
theorem foh_quaternion_rotation_ode
    {a : ℝ → ℝ} {v : ℝ → Vec3} {w : Vec3} {t : ℝ}
    (ha : HasDerivAt a (-(v t ⬝ᵥ w) / 2) t)
    (hv : HasDerivAt v ((1 / 2 : ℝ) • (a t • w + v t ⨯₃ w)) t) :
    HasDerivAt (fun s => fohQuaternionMatrix (a s) (v s))
      (fohQuaternionMatrix (a t) (v t) * skew w) t := by
  convert foh_quaternionMatrix_derivative ha hv using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fohQuaternionMatrix, lengthSq, skew, mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      vecMulVec, dotProduct, cross_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

@[simp] theorem foh_quaternionMatrix_initial : fohQuaternionMatrix 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [fohQuaternionMatrix, lengthSq, skew, vecMulVec]

/-- An actual unit-initialized quaternion trajectory yields an actual SO(3)
trajectory with the same right angular velocity. -/
theorem foh_quaternion_to_rotation
    (a : ℝ → ℝ) (v w : ℝ → Vec3)
    (ha : ∀ t, HasDerivAt a (-(v t ⬝ᵥ w t) / 2) t)
    (hv : ∀ t, HasDerivAt v ((1 / 2 : ℝ) • (a t • w t + v t ⨯₃ w t)) t)
    (ha0 : a 0 = 1) (hv0 : v 0 = 0) :
    ∃ R : ℝ → SO3, R 0 = 1 ∧
      (∀ t, (R t).val = fohQuaternionMatrix (a t) (v t)) ∧
      (∀ t, HasDerivAt (fun s => (R s).val) ((R t).val * skew (w t)) t) := by
  let R : ℝ → SO3 := fun t => fohQuaternionRotation (a t) (v t)
    (foh_quaternion_unit a v w ha hv ha0 hv0 t)
  refine ⟨R, ?_, fun _ => rfl, fun t => foh_quaternion_rotation_ode (ha t) (hv t)⟩
  apply Subtype.ext
  change fohQuaternionMatrix (a 0) (v 0) = 1
  rw [ha0, hv0, foh_quaternionMatrix_initial]

end GNC.Magnus
