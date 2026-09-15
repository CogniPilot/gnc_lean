import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-! Primal/dual certificates for a finite fuel-allocation linear program.
The solver is an untrusted candidate generator. All bounds, including lower
and upper actuator limits, are rows of A x ≤ b. -/
noncomputable section
open Finset
namespace GNC.FuelCertificate
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def Feasible (A : ι → κ → ℝ) (b : ι → ℝ) (x : κ → ℝ) : Prop :=
  ∀ i, (∑ j, A i j*x j) ≤ b i

def Cost (c x : κ → ℝ) : ℝ := ∑ j, c j*x j

theorem weak_duality (A : ι → κ → ℝ) (b : ι → ℝ) (c x : κ → ℝ)
    (ell : ι → ℝ) (hx : Feasible A b x) (hell : ∀ i, 0 ≤ ell i)
    (hstationary : ∀ j, (∑ i, ell i*A i j) = -c j) :
    -(∑ i, ell i*b i) ≤ Cost c x := by
  have h : (∑ i, ell i*(∑ j, A i j*x j)) ≤ ∑ i, ell i*b i :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hell i)
  have hid : (∑ i, ell i*(∑ j, A i j*x j)) = -Cost c x := by
    simp_rw [mul_sum, ← mul_assoc]
    rw [sum_comm]
    simp_rw [← sum_mul, hstationary, neg_mul]
    simp [Cost]
  rw [hid] at h
  linarith

theorem optimal (A : ι → κ → ℝ) (b : ι → ℝ) (c x : κ → ℝ)
    (ell : ι → ℝ) (hx : Feasible A b x) (hell : ∀ i, 0 ≤ ell i)
    (hstationary : ∀ j, (∑ i, ell i*A i j) = -c j)
    (hgap : Cost c x = -(∑ i, ell i*b i)) :
    Feasible A b x ∧ ∀ y, Feasible A b y → Cost c x ≤ Cost c y := by
  refine ⟨hx, fun y hy => ?_⟩
  rw [hgap]
  exact weak_duality A b c y ell hy hell hstationary

def boxLower (A : ι → κ → ℝ) (b : ι → ℝ) (c : κ → ℝ) (ell : ι → ℝ) : ℝ :=
  -(∑ i, ell i*b i)+∑ j, min 0 (c j+∑ i, ell i*A i j)

/-- A dual lower bound that remains valid when stationarity is inexact.
The signed residual is minimized over the unit actuator box. This accepts
rounded multipliers without trusting a numerical optimality tolerance. -/
theorem box_weak_duality (A : ι → κ → ℝ) (b : ι → ℝ) (c x : κ → ℝ)
    (ell : ι → ℝ) (hx : Feasible A b x) (hbox : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (hell : ∀ i, 0 ≤ ell i) : boxLower A b c ell ≤ Cost c x := by
  have hrow : (∑ i, ell i*(∑ j, A i j*x j)) ≤ ∑ i, ell i*b i :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hell i)
  have hg (j : κ) : min 0 (c j+∑ i, ell i*A i j) ≤
      (c j+∑ i, ell i*A i j)*x j := by
    by_cases hp : 0 ≤ c j+∑ i, ell i*A i j
    · rw [min_eq_left hp]
      exact mul_nonneg hp (hbox j).1
    · have hn := le_of_lt (lt_of_not_ge hp)
      rw [min_eq_right hn]
      nlinarith [(hbox j).2]
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset κ)) => hg j)
  have hid : (∑ j, (c j+∑ i, ell i*A i j)*x j) =
      Cost c x+∑ i, ell i*(∑ j, A i j*x j) := by
    simp_rw [add_mul, sum_add_distrib, sum_mul]
    rw [sum_comm (f := fun j i => ell i*A i j*x j)]
    simp_rw [mul_sum, mul_assoc]
    rfl
  rw [hid] at hs
  dsimp [boxLower]
  linarith

end GNC.FuelCertificate
