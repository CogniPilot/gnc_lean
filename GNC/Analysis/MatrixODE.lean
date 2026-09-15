import GNC.Analysis.LinearODE
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Continuous matrix fundamental solutions with the ordinary entrywise
matrix topology. Finite-dimensional linear maps reuse the existing linear
ODE existence theorem, without selecting a different matrix norm.
-/
noncomputable section
set_option autoImplicit false
namespace GNC.MatrixODE
open scoped Matrix.Norms.Elementwise
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_fundamental (A : ℝ → Matrix n n ℝ) (hA : Continuous A) :
    ∃ F : ℝ → Matrix n n ℝ, Continuous F ∧ F 0 = 1 ∧
      ∀ t, HasDerivAt F (A t*F t) t := by
  let left (t : ℝ) : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
    { toFun := fun B => A t*B
      map_add' := fun B C => Matrix.mul_add _ _ _
      map_smul' := fun r B => Matrix.mul_smul _ _ _ }
  let L := fun t => (left t).toContinuousLinearMap
  have hL : Continuous L := by
    apply continuous_clm_apply.mpr
    intro B
    change Continuous (fun t => A t*B)
    exact hA.mul continuous_const
  obtain ⟨F,hF₀,hF⟩ := GNC.LinearODE.exists_solution L hL (1:Matrix n n ℝ)
  refine ⟨F, continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt), hF₀, ?_⟩
  exact hF

end GNC.MatrixODE
