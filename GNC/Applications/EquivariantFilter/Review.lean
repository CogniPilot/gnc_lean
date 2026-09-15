import GNC.Lie.Euclidean
import GNC.Control.LogBackstepping

/-! Exact checks of the EqF paper, arXiv:2010.14666v3.
Equation (5) is tested using the innovations and error convention printed
immediately before it. A manuscript sign error does not establish what
code generated a published plot.
-/
noncomputable section
open Matrix Real
namespace GNC.Applications.EquivariantFilter
open GNC

/-- The exact squared-norm innovation has a PLUS linear term. -/
theorem constraint_innovation (estimate error : Vec3) :
    lengthSq (estimate+error)-lengthSq estimate =
      2*(estimate ⬝ᵥ error)+lengthSq error := by
  simp [lengthSq, dotProduct, Fin.sum_univ_succ]
  ring

theorem constraint_derivative (estimate error : Vec3) :
    HasDerivAt (fun s : ℝ => lengthSq (estimate+s • error)-lengthSq estimate)
      (2*(estimate ⬝ᵥ error)) 0 := by
  have h : HasDerivAt (fun s : ℝ => estimate+s • error) error 0 := by
    simpa only [Pi.add_apply,one_smul,zero_add,id_eq] using
      (hasDerivAt_const (0:ℝ) estimate).add ((hasDerivAt_id (0:ℝ)).smul_const error)
  simpa using (LogBackstepping.lengthSq_derivative h).sub_const (lengthSq estimate)

/-- Even with true scalar bearing fixed at unit length, varying the
embedded estimate produces the opposite first derivative to Eq. (5). -/
theorem equation5_sign_counterexample :
    HasDerivAt (fun s : ℝ => 1-(1+s)^2) (-2) 0 ∧
    HasDerivAt (fun s : ℝ => -2*(1+s)*(1-(1+s))) 2 0 := by
  constructor
  · convert (((hasDerivAt_id (0:ℝ)).const_add 1).pow 2).const_sub 1 using 1 <;> norm_num
  · convert ((hasDerivAt_id (0:ℝ)).const_mul 2).add
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul 2) using 1
    · ext s; simp only [Pi.add_apply,Pi.pow_apply,id_eq]; ring
    · norm_num

/-- Equation (51), as printed, identifies antipodal directed bearings.
The linked example code uses abs(arccos(dot)) instead. -/
theorem equation51_antipodal_counterexample :
    arccos (|(-1:ℝ)|)=0 ∧ arccos (-1:ℝ)=π := by simp

end GNC.Applications.EquivariantFilter
