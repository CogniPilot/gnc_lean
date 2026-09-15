import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! Reproduction of the quadratic-image identity underlying Althoff (HSCC
2013), Theorem 1. We retain ordered pairs of generators; collecting the two
off-diagonal terms gives the paper's symmetric storage convention. The
parameter is shared across every term, so the image equality is exact.

The separate set-splitting theorem retains both mixed products. They cannot
be dropped merely by making parameters independent. These are algebraic
set certificates, not a proof of a numerical reachability implementation.
-/
noncomputable section
open scoped BigOperators
namespace GNC.QuadraticReachability
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] {ι : Type*} [Fintype ι]

def zonotope (c : E) (g : ι → E) : Set E :=
  {x | ∃ β : ι → ℝ, (∀ j, |β j| ≤ 1) ∧ x = c + ∑ j, β j • g j}

def quadraticPolynomial (Q : E →ₗ[ℝ] E →ₗ[ℝ] F) (c : E) (g : ι → E)
    (β : ι → ℝ) : F :=
  Q c c + ∑ j, β j • (Q c (g j) + Q (g j) c) +
    ∑ j, ∑ k, (β j * β k) • Q (g j) (g k)

/-- Theorem 1's exact dependent polynomial, for any vector-valued bilinear
map. No symmetry or positive definiteness of Q is required. -/
theorem quadratic_expansion (Q : E →ₗ[ℝ] E →ₗ[ℝ] F) (c : E)
    (g : ι → E) (β : ι → ℝ) :
    Q (c + ∑ j, β j • g j) (c + ∑ j, β j • g j) =
      quadraticPolynomial Q c g β := by
  simp only [quadraticPolynomial, map_add, map_sum, LinearMap.add_apply,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_add,
    Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  have hs : (∑ k, ∑ j, (β k * β j) • Q (g j) (g k)) =
      ∑ j, ∑ k, (β j * β k) • Q (g j) (g k) := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hs]
  abel

theorem quadratic_image (Q : E →ₗ[ℝ] E →ₗ[ℝ] F) (c : E) (g : ι → E) :
    (fun x => Q x x) '' zonotope c g =
      {y | ∃ β : ι → ℝ, (∀ j, |β j| ≤ 1) ∧ y = quadraticPolynomial Q c g β} := by
  ext y
  constructor
  · rintro ⟨x, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, quadratic_expansion Q c g β⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨c + ∑ j, β j • g j, ⟨β, hβ, rfl⟩, quadratic_expansion Q c g β⟩

theorem split_identity (Q : E →ₗ[ℝ] E →ₗ[ℝ] F) (x y : E) :
    Q (x+y) (x+y) = Q x x + (Q x y + Q y x) + Q y y := by
  simp only [map_add, LinearMap.add_apply]
  abel

def addSet (S T : Set E) : Set E := {z | ∃ x ∈ S, ∃ y ∈ T, z = x+y}

/-- A sound independent enclosure of a split quadratic image includes the
cross term. Its inclusion can be strict because it forgets dependencies. -/
theorem split_enclosure (Q : E →ₗ[ℝ] E →ₗ[ℝ] F) (S T : Set E) :
    (fun x => Q x x) '' addSet S T ⊆
      addSet (addSet ((fun x => Q x x) '' S)
        {z | ∃ x ∈ S, ∃ y ∈ T, z = Q x y + Q y x})
        ((fun y => Q y y) '' T) := by
  rintro z ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  exact ⟨Q x x + (Q x y + Q y x),
    ⟨Q x x, ⟨x, hx, rfl⟩, Q x y + Q y x, ⟨x, hx, y, hy, rfl⟩, rfl⟩,
    Q y y, ⟨y, hy, rfl⟩, split_identity Q x y⟩

end GNC.QuadraticReachability
