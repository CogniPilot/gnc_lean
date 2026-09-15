import GNC.Magnus.MagnusAlgebra
import GNC.Lie.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The mixed-invariant paper's closed exponential also applies to every
finite Magnus Lie polynomial in the time-extended SE₂(3) algebra. The time
corner is a scalar multiple of one fixed square-zero matrix. Individual
square-zero samples alone would not imply this closure. No convergence or
exactness of a truncated Magnus exponent is asserted here.
-/
noncomputable section
namespace GNC.Magnus
open Matrix
open scoped Matrix.Norms.Operator

def timeCorner (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,β;0,0]

@[simp] theorem timeCorner_square (β : ℝ) : timeCorner β^2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeCorner, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem split_extended (x : LogState) (β : ℝ) :
    splitMatrix (extended x β) =
      Preintegration.block (skew (x 2)) (columns (x 1) (x 0)) (timeCorner β) := by
  ext (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;>
    simp [splitMatrix, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      extended, hat, kinematicC, Preintegration.block, columns, skew, timeCorner,
      finSumFinEquiv]

/-- This is a relation of the actual 5×5 matrix, with its angular norm
derived from the skew block and its time-corner nilpotence discharged. -/
theorem extended_power_five (x : LogState) (β : ℝ) :
    extended x β^5 = -(enorm (x 2)^2) • extended x β^3 := by
  apply splitMatrix.injective
  simp only [map_pow, map_smul, split_extended]
  exact Preintegration.block_relation _ _ _ _ (skew_cube (x 2)) (timeCorner_square β)

/-- The five coefficients requested by Cayley--Hamilton. The nonpolynomial
coefficients are precisely f₂ and f₃ of the mixed-invariant paper. -/
theorem exp_extended (x : LogState) (β t : ℝ) (hx : enorm (x 2) ≠ 0) :
    NormedSpace.exp (t • extended x β) =
      1+t • extended x β+(t^2/2) • extended x β^2+
        Preintegration.f₂ (enorm (x 2)) t • extended x β^3+
        Preintegration.f₃ (enorm (x 2)) t • extended x β^4 :=
  Preintegration.exp_polynomial _ _ _ hx (extended_power_five x β)

theorem extended_zero_cube (x : LogState) (β : ℝ) (hx : x 2 = 0) :
    extended x β^3 = 0 := by
  apply splitMatrix.injective
  rw [map_pow, map_zero, split_extended, hx, skew_zero]
  simpa using Preintegration.block_power
    (0 : Matrix (Fin 3) (Fin 3) ℝ) (columns (x 1) (x 0)) (timeCorner β)
    (timeCorner_square β) 1

theorem exp_extended_zero (x : LogState) (β t : ℝ) (hx : x 2 = 0) :
    NormedSpace.exp (t • extended x β) =
      1+t • extended x β+(t^2/2) • extended x β^2 := by
  have h3 := extended_zero_cube x β hx
  have h4 : extended x β^4 = 0 := by rw [show 4 = 3+1 by rfl, pow_succ, h3, zero_mul]
  have h5 : extended x β^5 = -(1^2 : ℝ) • extended x β^3 := by
    calc
      _ = extended x β^4*extended x β := pow_succ _ 4
      _ = _ := by rw [h4, zero_mul, h3, smul_zero]
  simpa [Preintegration.polynomial, h3, h4] using
    Preintegration.exp_polynomial (extended x β) 1 t (by norm_num) h5

def extendedLinear : (LogState × ℝ) →ₗ[ℝ] Mat5 where
  toFun z := extended z.1 z.2
  map_add' := by
    intro x y
    change hatLinear (x.1+y.1)+(x.2+y.2) • kinematicC =
      (hatLinear x.1+x.2 • kinematicC)+(hatLinear y.1+y.2 • kinematicC)
    rw [map_add, add_smul]
    abel
  map_smul' := by
    intro c x
    change hatLinear (c • x.1)+(c*x.2) • kinematicC =
      c • (hatLinear x.1+x.2 • kinematicC)
    rw [map_smul, smul_add, smul_smul]

/-- Actual mathlib Lie subalgebra: finite sums, scalar multiples and arbitrary
nested commutators preserve the hypothesis needed by `exp_extended`. -/
def timeExtendedAlgebra : LieSubalgebra ℝ Mat5 where
  __ := LinearMap.range extendedLinear
  lie_mem' {a b} ha hb := by
    obtain ⟨⟨x,β⟩, rfl⟩ := ha
    obtain ⟨⟨y,γ⟩, rfl⟩ := hb
    exact ⟨(extendedBracket x y β γ,0), (extended_commutator x y β γ).symm⟩

theorem extended_mem (x : LogState) (β : ℝ) : extended x β ∈ timeExtendedAlgebra :=
  ⟨(x,β),rfl⟩

/-- Applies to a finite Magnus exponent after its Lie-algebra membership is
established. It does not identify that exponent with the exact flow log. -/
theorem member_power_five (M : Mat5) (hM : M ∈ timeExtendedAlgebra) :
    ∃ θ : ℝ, 0 ≤ θ ∧ M^5 = -(θ^2) • M^3 := by
  obtain ⟨⟨x,β⟩, rfl⟩ := hM
  exact ⟨enorm (x 2), enorm_nonneg _, extended_power_five x β⟩

theorem finite_sum_mem {I : Type*} (s : Finset I) (M : I → Mat5) (c : I → ℝ)
    (hM : ∀ i ∈ s, M i ∈ timeExtendedAlgebra) :
    (∑ i ∈ s, c i • M i) ∈ timeExtendedAlgebra := by
  apply timeExtendedAlgebra.sum_mem
  intro i hi
  exact timeExtendedAlgebra.smul_mem (c i) (hM i hi)

/-- Integrating coordinates and then lifting is exact. This supplies the
integral step needed in Magnus terms, in addition to bracket closure. -/
theorem integral_extended (u : ℝ → LogState × ℝ) (a b : ℝ)
    (hu : IntervalIntegrable u MeasureTheory.volume a b) :
    (∫ t in a..b, extendedLinear (u t)) = extendedLinear (∫ t in a..b, u t) := by
  let L : (LogState × ℝ) →L[ℝ] Mat5 :=
    { extendedLinear with cont := extendedLinear.continuous_of_finiteDimensional }
  exact L.intervalIntegral_comp_comm hu

theorem integral_extended_mem (u : ℝ → LogState × ℝ) (a b : ℝ)
    (hu : IntervalIntegrable u MeasureTheory.volume a b) :
    (∫ t in a..b, extendedLinear (u t)) ∈ timeExtendedAlgebra := by
  rw [integral_extended u a b hu]
  exact ⟨_,rfl⟩

theorem commutator_time_zero (x y : LogState) (β γ : ℝ) :
    (extended x β*extended y γ-extended y γ*extended x β) 3 4 = 0 := by
  rw [extended_commutator]
  simp [extended, hat, kinematicC]

/-- A two-node left-Magnus exponent, including the time corner. The same
coefficient formula can therefore be used after this commutator correction. -/
theorem gauss_extended (x y : LogState) (β γ h : ℝ) :
    (h/2) • (extended x β+extended y γ)-
      (Real.sqrt 3*h^2/12) • (extended x β*extended y γ-extended y γ*extended x β) =
      extended ((h/2) • (x+y)-(Real.sqrt 3*h^2/12) • extendedBracket x y β γ)
        ((h/2)*(β+γ)) := by
  rw [extended_commutator]
  change (h/2) • (extendedLinear (x,β)+extendedLinear (y,γ))-
    (Real.sqrt 3*h^2/12) • extendedLinear (extendedBracket x y β γ,0) = _
  rw [← map_add, ← map_smul, ← map_smul, ← map_sub]
  simp [extendedLinear, smul_eq_mul]

end GNC.Magnus
