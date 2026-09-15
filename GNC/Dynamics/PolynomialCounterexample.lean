import GNC.Dynamics.MixedClassification
import Mathlib.Analysis.Matrix.Normed

/-! Polynomial group-affine dynamics on the standard upper-unitriangular
3-by-3 matrix group need not admit state-independent ambient mixed
coefficients. Thus analyticity or polynomial dependence alone cannot
repair the conjecture. The matrix group laws are checked explicitly.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GNC.PolynomialCounterexample

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
def state (x y z : ℝ) : Mat3 := !![1,x,z;0,1,y;0,0,1]
def field (X : Mat3) : Mat3 := !![0,X 1 2,(X 1 2)^2/2;0,0,0;0,0,0]

theorem state_mul (x y z a b c : ℝ) :
    state x y z*state a b c = state (x+a) (y+b) (z+c+x*b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [state, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

@[simp] theorem state_zero : state 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [state]

def stateUnit (x y z : ℝ) : Mat3ˣ :=
  ⟨state x y z,state (-x) (-y) (x*y-z),
    by rw [state_mul]; convert state_zero using 1 <;> congr 1 <;> ring,
    by rw [state_mul]; convert state_zero using 1 <;> congr 1 <;> ring⟩

def group : Subgroup Mat3ˣ where
  carrier := {X | ∃ x y z, X.val = state x y z}
  one_mem' := ⟨0,0,0,state_zero.symm⟩
  mul_mem' := by
    rintro X Y ⟨x,y,z,hX⟩ ⟨a,b,c,hY⟩
    exact ⟨x+a,y+b,z+c+x*b,by simpa only [Units.val_mul,hX,hY] using state_mul x y z a b c⟩
  inv_mem' := by
    rintro X ⟨x,y,z,hX⟩
    have he : X = stateUnit x y z := Units.ext hX
    exact ⟨-x,-y,x*y-z,by rw [he]; rfl⟩

theorem group_affine : Estimation.GroupAffineOn group field := by
  rintro X ⟨x,y,z,hX⟩ Y ⟨a,b,c,hY⟩
  simp only [Units.val_mul,hX,hY,state_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [field,state,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem no_mixed_representation :
    ¬ ∃ M N : Mat3, ∀ x y z : ℝ, field (state x y z) = M*state x y z+state x y z*N := by
  rintro ⟨M,N,h⟩
  have h₀ := congrArg (fun X : Mat3 => X 0 1) (h 0 0 0)
  have h₁ := congrArg (fun X : Mat3 => X 0 1) (h 0 1 0)
  norm_num [field,state,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.cons_val_two] at h₀ h₁
  linarith

/-- Globally defined trajectories stay inside the displayed matrix
group and solve the polynomial vector field. -/
theorem trajectory_derivative (x y z t : ℝ) :
    HasDerivAt (fun s => state (x+s*y) y (z+s*(y^2/2)))
      (field (state (x+t*y) y (z+t*(y^2/2)))) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> simp only [state,field,Matrix.of_apply,Matrix.cons_val] <;>
    first
    | exact hasDerivAt_const t _
    | simpa using ((hasDerivAt_id t).mul_const y).const_add x
    | simpa using ((hasDerivAt_id t).mul_const (y^2/2)).const_add z

/-- The corrected central coordinate is constant along these flows;
the remaining coordinates obey x'=y, y'=0. -/
theorem central_coordinate_constant (x y z t : ℝ) :
    (z+t*(y^2/2))-(x+t*y)*y/2 = z-x*y/2 := by ring

end GNC.PolynomialCounterexample
