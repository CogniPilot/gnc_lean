import GNC.Preintegration.ClosedForm
import GNC.Applications.Rendezvous.SingularTimes

/-! The closed HCW transition matrix, proved equal to the actual matrix
exponential. This instantiates the closed-form machinery for the circular
coasting model instead of assuming the entries of its STM. -/
noncomputable section
open Matrix Real
open scoped Matrix Matrix.Norms.Operator
namespace GNC.HCWMatrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Mat6 := Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ

def gravity (n : ℝ) : Mat3 := !![3*n^2,0,0; 0,0,0; 0,0,-n^2]
def coriolis (n : ℝ) : Mat3 := !![0,2*n,0; -2*n,0,0; 0,0,0]
def generator (n : ℝ) : Mat6 := fromBlocks 0 1 (gravity n) (coriolis n)

def square (n : ℝ) : Mat6 := fromBlocks (gravity n) (coriolis n)
  !![0,0,0; -6*n^3,0,0; 0,0,0] !![-n^2,0,0; 0,-4*n^2,0; 0,0,-n^2]

def cube (n : ℝ) : Mat6 := fromBlocks
  !![0,0,0; -6*n^3,0,0; 0,0,0] !![-n^2,0,0; 0,-4*n^2,0; 0,0,-n^2]
  !![-3*n^4,0,0; 0,0,0; 0,0,n^4] !![0,-2*n^3,0; 2*n^3,0,0; 0,0,0]

theorem generator_square (n : ℝ) : generator n^2 = square n := by
  simp only [generator, pow_two, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [square, gravity, coriolis, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ] <;> ring

theorem generator_cube (n : ℝ) : generator n^3 = cube n := by
  rw [pow_succ' (generator n) 2, generator_square]
  simp only [generator, square, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [cube, gravity, coriolis, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ] <;> ring

theorem generator_fourth (n : ℝ) : generator n^4 = -(n^2) • generator n^2 := by
  rw [pow_succ' (generator n) 3, generator_cube, generator_square]
  simp only [generator, cube, fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [square, gravity, coriolis, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ] <;> ring

theorem generator_fifth (n : ℝ) : generator n^5 = -(n^2) • generator n^3 := by
  rw [pow_succ (generator n) 4, generator_fourth, Matrix.smul_mul, ← pow_succ]

def rr (n t : ℝ) : Mat3 :=
  !![4-3*cos (n*t),0,0; 6*(sin (n*t)-n*t),1,0; 0,0,cos (n*t)]
def rv (n t : ℝ) : Mat3 :=
  !![sin (n*t)/n,2*(1-cos (n*t))/n,0;
    -2*(1-cos (n*t))/n,(4*sin (n*t)-3*n*t)/n,0; 0,0,sin (n*t)/n]
def vr (n t : ℝ) : Mat3 :=
  !![3*n*sin (n*t),0,0; 6*n*(cos (n*t)-1),0,0; 0,0,-n*sin (n*t)]
def vv (n t : ℝ) : Mat3 :=
  !![cos (n*t),2*sin (n*t),0; -2*sin (n*t),4*cos (n*t)-3,0; 0,0,cos (n*t)]
def stm (n t : ℝ) : Mat6 := fromBlocks (rr n t) (rv n t) (vr n t) (vv n t)

/-- The entries in (91) belong to the actual HCW fundamental solution. -/
theorem stm_exp (n t : ℝ) (hn : n ≠ 0) :
    stm n t = NormedSpace.exp (t • generator n) := by
  rw [Preintegration.exp_polynomial _ _ _ hn (generator_fifth n)]
  simp only [Preintegration.polynomial, generator_fourth, generator_cube, generator_square]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [stm, rr, rv, vr, vv, generator, square, cube, gravity, coriolis,
      Preintegration.f₂, Preintegration.f₃] <;> field_simp <;> ring

@[simp] theorem stm_initial (n : ℝ) : stm n 0 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [stm, rr, rv, vr, vv, Matrix.one_apply] <;> (intro h; cases h)

theorem stm_derivative (n t : ℝ) (hn : n ≠ 0) :
    HasDerivAt (stm n) (generator n*stm n t) t := by
  have hf : stm n = fun s => NormedSpace.exp (s • generator n) := funext (fun s => stm_exp n s hn)
  rw [hf]
  exact hasDerivAt_exp_smul_const' (generator n) t

theorem stm_inverse (n t : ℝ) (hn : n ≠ 0) : stm n t*stm n (-t) = 1 := by
  rw [stm_exp n t hn, stm_exp n (-t) hn, neg_smul, MixedInvariant.exp_cancel]

theorem rv_normalized (t : ℝ) : rv 1 t = SingularTimes.pv t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rv, SingularTimes.pv]

theorem rv_scaled (n t : ℝ) : rv n t = (1/n) • SingularTimes.pv (n*t) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rv, SingularTimes.pv, div_eq_mul_inv] <;> ring

/-- The additional singularity is now exhibited in a proven STM block. -/
theorem exists_additional_singular_stm : ∃ t : ℝ,
    5*π/2 < t ∧ t < 3*π ∧ ((stm 1 t).toBlocks₁₂).det = 0 ∧ sin t ≠ 0 := by
  simpa only [stm, toBlocks_fromBlocks₁₂, rv_normalized] using
    SingularTimes.exists_additional_singularity

end GNC.HCWMatrix
