import GNC.Dynamics.MixedLogLinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! A smooth group-affine field need not be ambient mixed invariant in
the given matrix representation. The nonzero real scalars are GL(1, ℝ);
the same obstruction already holds on the connected positive component.
-/
noncomputable section
open scoped ContDiff
namespace GNC.GroupAffineCounterexample

def field (x : ℝ) : ℝ := x * Real.log x

def positiveScalars : Subgroup ℝˣ where
  carrier := {X | 0 < X.val}
  one_mem' := by norm_num
  mul_mem' := by
    intro a b ha hb
    exact mul_pos (show 0 < a.val from ha) (show 0 < b.val from hb)
  inv_mem' := by
    intro x hx
    change 0 < (x⁻¹).val
    simpa using inv_pos.mpr (show 0 < x.val from hx)

theorem group_affine : Estimation.GroupAffine field := by
  intro X Y
  simp only [Units.val_mul, field, Real.log_one, mul_zero]
  rw [Real.log_mul (Units.ne_zero X) (Units.ne_zero Y)]
  ring

theorem group_affine_positive : Estimation.GroupAffineOn positiveScalars field :=
  fun X _ Y _ => group_affine X Y

theorem smooth : ContDiffOn ℝ ∞ field {x : ℝ | x ≠ 0} :=
  contDiffOn_id.mul Real.contDiffOn_log

theorem field_derivative {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt field (Real.log x+1) x := by
  simpa [field, hx] using (hasDerivAt_id x).mul (Real.hasDerivAt_log hx)

/-- Group affinity does not make the ambient state Hessian vanish. -/
theorem second_derivative_at_one : HasDerivAt (deriv field) 1 1 := by
  have h := ((Real.hasDerivAt_log (by norm_num : (1:ℝ) ≠ 0)).add_const 1)
  apply (show HasDerivAt (fun x : ℝ => Real.log x+1) 1 1 by simpa using h).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (by norm_num : (1:ℝ) ≠ 0)] with x hx
  exact (field_derivative hx).deriv

theorem not_mixed_on_positive :
    ¬ ∃ M N : ℝ, ∀ x > 0, field x = M*x+x*N := by
  rintro ⟨M,N,h⟩
  have h₁ := h 1 (by norm_num)
  simp only [field, Real.log_one, mul_zero, mul_one, one_mul] at h₁
  have he := h (Real.exp 1) (Real.exp_pos 1)
  simp only [field, Real.log_exp, mul_one] at he
  have hz : M*Real.exp 1+Real.exp 1*N = 0 := by
    calc
      _ = (M+N)*Real.exp 1 := by ring
      _ = 0 := by rw [← h₁, zero_mul]
  rw [hz] at he
  exact (Real.exp_ne_zero 1) he

/-- The counterexample still has exact linear dynamics in logarithmic
coordinates: it refutes mixed-form universality, not log-linearity. -/
theorem logarithmic_dynamics {x : ℝ → ℝ} {t : ℝ} (hpos : 0 < x t)
    (hx : HasDerivAt x (field (x t)) t) :
    HasDerivAt (fun s => Real.log (x s)) (Real.log (x t)) t := by
  convert (Real.hasDerivAt_log hpos.ne').comp t hx using 1
  dsimp [field]
  field_simp

/-- A global positive solution for every initial logarithm, showing
that the counterexample does not leave the positive-scalar manifold. -/
theorem positive_solution (ξ₀ t : ℝ) :
    0 < Real.exp (Real.exp t * ξ₀) ∧
    HasDerivAt (fun s => Real.exp (Real.exp s * ξ₀))
      (field (Real.exp (Real.exp t * ξ₀))) t := by
  refine ⟨Real.exp_pos _, ?_⟩
  simpa only [field, Real.log_exp, mul_comm] using
    ((Real.hasDerivAt_exp t).mul_const ξ₀).exp

end GNC.GroupAffineCounterexample
