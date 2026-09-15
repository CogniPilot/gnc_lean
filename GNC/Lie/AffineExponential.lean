import GNC.Preintegration.ClosedForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! An everywhere-defined exponential for any number of translation columns.
The matrix integral avoids removable singularities in trigonometric quotients
and works for scaling, rotation, and general linear generators alike. -/
noncomputable section
open Matrix NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator
namespace GNC.AffineExponential
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def primitive (A : Matrix m m ℝ) (t : ℝ) : Matrix m m ℝ :=
  ∫ s in (0:ℝ)..t, exp (s • A)

theorem primitive_derivative (A : Matrix m m ℝ) (t : ℝ) :
    HasDerivAt (primitive A) (exp (t • A)) t := by
  have hc : Continuous (fun s : ℝ => exp (s • A)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_exp_smul_const A s).continuousAt
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem primitive_zero_generator (t : ℝ) :
    primitive (0 : Matrix m m ℝ) t = t • 1 := by simp [primitive]

theorem mul_rectangular_const_derivative
    (A : ℝ → Matrix m m ℝ) (U : Matrix m n ℝ)
    {A' : Matrix m m ℝ} {t : ℝ} (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => A s*U) (A'*U) t := by
  let L : Matrix m m ℝ →ₗ[ℝ] Matrix m n ℝ := {
    toFun := fun B => B*U
    map_add' := fun B C => Matrix.add_mul B C U
    map_smul' := fun r B => by simp }
  exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hA

theorem fromBlocks_derivative
    (A : ℝ → Matrix m m ℝ) (B : ℝ → Matrix m n ℝ)
    {A' : Matrix m m ℝ} {B' : Matrix m n ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => fromBlocks (A s) (B s) 0 (1 : Matrix n n ℝ))
      (fromBlocks A' B' 0 0) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j
    | inr j => exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i) j
  | inr i =>
    cases j with
    | inl j => exact hasDerivAt_const t 0
    | inr j => exact hasDerivAt_const t ((1 : Matrix n n ℝ) i j)

/-- Actual mathlib exponential, for arbitrary linear generator A and
arbitrary number of translation columns U. No inverse of A is needed. -/
theorem exp_block (A : Matrix m m ℝ) (U : Matrix m n ℝ) (t : ℝ) :
    exp (t • Preintegration.block A U 0) =
      fromBlocks (exp (t • A)) (primitive A t*U) 0 1 := by
  let F : ℝ → Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    fun s => fromBlocks (exp (s • A)) (primitive A s*U) 0 1
  have hd (s : ℝ) : HasDerivAt F
      (0*F s+F s*Preintegration.block A U 0) s := by
    convert fromBlocks_derivative (fun r => exp (r • A))
      (fun r => primitive A r*U) (hasDerivAt_exp_smul_const A s)
      (mul_rectangular_const_derivative (primitive A) U (primitive_derivative A s)) using 1
    simp [F, Preintegration.block, fromBlocks_multiply]
  have hi : F 0 = 1 := by simp [F, primitive, fromBlocks_one]
  have he := MixedInvariant.flow_unique 0 (Preintegration.block A U 0) 1 F hd hi
  simpa [F, MixedInvariant.flow] using (congrFun he t).symm

/-- Correct value at simultaneous zero angle and zero log-scale. -/
theorem pure_translation (U : Matrix m n ℝ) :
    exp (Preintegration.block (0 : Matrix m m ℝ) U 0) =
      fromBlocks 1 U 0 1 := by
  simpa [primitive_zero_generator] using exp_block (0 : Matrix m m ℝ) U 1

end GNC.AffineExponential
