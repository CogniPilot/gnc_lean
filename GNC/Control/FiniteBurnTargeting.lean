import Mathlib.Data.Matrix.Mul

/-! Composition of two finite-burn STM/input maps separated by a coast.
All states and inputs use the same coordinates at handoffs. This identity
does not assert controllability, fuel optimality or physical error bounds. -/
namespace GNC.FiniteBurnTargeting
open Matrix
variable {n m : Type*} [Fintype n] [Fintype m]
variable {R : Type*} [Semiring R]

theorem two_burn_arrival (P₁ Pc P₂ : Matrix n n R) (G₁ G₂ : Matrix n m R)
    (x : n → R) (u₁ u₂ : m → R) :
    P₂ *ᵥ (Pc *ᵥ (P₁ *ᵥ x + G₁ *ᵥ u₁)) + G₂ *ᵥ u₂ =
      (P₂*Pc*P₁) *ᵥ x + (P₂*Pc*G₁) *ᵥ u₁ + G₂ *ᵥ u₂ := by
  simp only [mulVec_add, mulVec_mulVec, Matrix.mul_assoc]

end GNC.FiniteBurnTargeting
