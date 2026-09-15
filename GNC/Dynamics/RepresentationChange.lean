import GNC.Dynamics.GroupAffineCounterexample
import Mathlib.Analysis.Matrix.Normed

/-! A concrete change of faithful group representation removes the
scalar x log x obstruction. Positive scalars map to unipotent 2-by-2
matrices using their logarithm. The resulting mixed coefficients are
constant and invertible, but outside the represented Lie algebra.
-/
noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GNC.RepresentationChange

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
def shear (z : ℝ) : Mat2 := !![1,z;0,1]
def direction (z : ℝ) : Mat2 := !![0,z;0,0]
def generator : Mat2 := !![2,0;0,1]

theorem shear_mul (x y : ℝ) : shear x * shear y = shear (x+y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

@[simp] theorem shear_zero : shear 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [shear]

theorem shear_injective : Function.Injective shear := by
  intro x y h
  exact congrArg (fun X : Mat2 => X 0 1) h

def shearUnit (z : ℝ) : Mat2ˣ :=
  ⟨shear z,shear (-z),by rw [shear_mul]; simp,by rw [shear_mul]; simp⟩

/-- A faithful group homomorphism, not just an arbitrary coordinate map. -/
def positiveEmbedding : GroupAffineCounterexample.positiveScalars →* Mat2ˣ where
  toFun x := shearUnit (Real.log (x.val.val))
  map_one' := by apply Units.ext; simp [shearUnit]
  map_mul' x y := by
    apply Units.ext
    change shear (Real.log (x.val.val*y.val.val)) = _
    rw [Real.log_mul (Units.ne_zero x.val) (Units.ne_zero y.val)]
    exact (shear_mul _ _).symm

theorem positiveEmbedding_injective : Function.Injective positiveEmbedding := by
  intro x y h
  have hs := shear_injective (congrArg Units.val h)
  change Real.log x.val.val = Real.log y.val.val at hs
  have he := congrArg Real.exp hs
  have hx : 0 < x.val.val := x.property
  have hy : 0 < y.val.val := y.property
  simp only [Real.exp_log hx, Real.exp_log hy] at he
  apply Subtype.ext
  exact Units.ext he

theorem mixed_identity (z : ℝ) :
    generator*shear z-shear z*generator = direction z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator, shear, direction, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem generator_invertible : IsUnit generator := by
  refine ⟨⟨generator,!![1/2,0;0,1],?_,?_⟩,rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [generator, Matrix.mul_apply, Fin.sum_univ_succ]

theorem generator_outside_algebra : ∀ z : ℝ, generator ≠ direction z := by
  intro z h
  have h₀ := congrArg (fun X : Mat2 => X 0 0) h
  norm_num [generator, direction] at h₀

def directionLinear : ℝ →ₗ[ℝ] Mat2 where
  toFun := direction
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [direction]
  map_smul' r x := by ext i j; fin_cases i <;> fin_cases j <;> simp [direction]

theorem shear_derivative {z : ℝ → ℝ} {v t : ℝ} (hz : HasDerivAt z v t) :
    HasDerivAt (fun s => shear (z s)) (direction v) t := by
  have h := directionLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hz
  convert h.const_add (1:Mat2) using 1
  funext s
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, directionLinear, direction]

/-- The same scalar dynamics that have no mixed representation in
GL(1) do have one after the faithful logarithmic group embedding. -/
theorem scalar_dynamics_become_mixed {x : ℝ → ℝ} {t : ℝ} (hx : 0 < x t)
    (hd : HasDerivAt x (GroupAffineCounterexample.field (x t)) t) :
    HasDerivAt (fun s => shear (Real.log (x s)))
      (generator*shear (Real.log (x t))-shear (Real.log (x t))*generator) t := by
  rw [mixed_identity]
  exact shear_derivative (GroupAffineCounterexample.logarithmic_dynamics hx hd)

end GNC.RepresentationChange
