import GNC.Dynamics.MixedClassification
import Mathlib.Analysis.Matrix.Normed

/-! Even linear dependence on ambient matrix entries does not suffice
in an arbitrary fixed representation. This additive two-dimensional
group is represented by square-zero 5-by-5 matrices. The group-affine
field is the restriction of a linear map on all ambient matrices.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GNC.LinearRepresentationCounterexample

abbrev Mat5 := Matrix (Fin 5) (Fin 5) ℝ
def state (a b : ℝ) : Mat5 :=
  !![1,0,a,b,0; 0,1,0,0,b; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1]
def direction (a : ℝ) : Mat5 :=
  !![0,0,0,a,0; 0,0,0,0,a; 0,0,0,0,0; 0,0,0,0,0; 0,0,0,0,0]
def field (X : Mat5) : Mat5 := direction (X 0 2)

theorem state_mul (a b c d : ℝ) : state a b*state c d = state (a+c) (b+d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [state,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

@[simp] theorem state_zero : state 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [state]

def stateUnit (a b : ℝ) : Mat5ˣ :=
  ⟨state a b,state (-a) (-b),by rw [state_mul]; simp,by rw [state_mul]; simp⟩

def group : Subgroup Mat5ˣ where
  carrier := {X | ∃ a b, X.val = state a b}
  one_mem' := ⟨0,0,state_zero.symm⟩
  mul_mem' := by
    rintro X Y ⟨a,b,hX⟩ ⟨c,d,hY⟩
    exact ⟨a+c,b+d,by simpa only [Units.val_mul,hX,hY] using state_mul a b c d⟩
  inv_mem' := by
    rintro X ⟨a,b,hX⟩
    have he : X = stateUnit a b := Units.ext hX
    exact ⟨-a,-b,by rw [he]; rfl⟩

/-- Linearity holds on the entire ambient matrix space. -/
def fieldLinear : Mat5 →ₗ[ℝ] Mat5 where
  toFun := field
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [field,direction]
  map_smul' r X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [field,direction]

theorem group_affine : Estimation.GroupAffineOn group field := by
  rintro X ⟨a,b,hX⟩ Y ⟨c,d,hY⟩
  simp only [Units.val_mul,hX,hY,state_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [field,direction,state,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.cons_val_two] <;> ring

theorem no_mixed_representation :
    ¬ ∃ M N : Mat5, ∀ a b : ℝ, field (state a b) = M*state a b+state a b*N := by
  rintro ⟨M,N,h⟩
  have h₀ := congrArg (fun X : Mat5 => X 1 4) (h 0 0)
  have h₁ := congrArg (fun X : Mat5 => X 1 4) (h 1 0)
  norm_num [field,direction,state,Matrix.mul_apply,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_four] at h₀ h₁
  linarith

theorem trajectory_derivative (a b t : ℝ) :
    HasDerivAt (fun s => state a (b+s*a)) (field (state a (b+t*a))) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [state,field,direction,Matrix.of_apply,Matrix.cons_val] <;>
    first
    | exact hasDerivAt_const t _
    | simpa using ((hasDerivAt_id t).mul_const a).const_add b

end GNC.LinearRepresentationCounterexample
