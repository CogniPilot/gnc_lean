import GNC.Control.Contraction

/-! Energy and port balances. Skew interconnection supplies energy
cancellation, not automatic incremental contraction. No Poisson/Jacobi
identity or physical Hamiltonian interpretation is inferred from skewness.
-/
noncomputable section
open Real
namespace GNC.PortHamiltonian
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

theorem power_balance (g Jg Rg Bu : E) (u y : U)
    (hJ : inner ℝ g Jg = 0) (hport : inner ℝ g Bu = inner ℝ y u) :
    inner ℝ g (Jg-Rg+Bu) = -inner ℝ g Rg+inner ℝ y u := by
  simp only [inner_add_right, inner_sub_right, hJ, hport]
  ring

/-- Passivity follows from the actual derivative of H and nonnegative
dissipation, for arbitrary state-dependent skew interconnection. -/
theorem hamiltonian_derivative (H : E → ℝ) {x : ℝ → E} {t : ℝ}
    (g Jg Rg Bu : E) (u y : U)
    (hH : HasFDerivAt H (innerSL ℝ g) (x t))
    (hx : HasDerivAt x (Jg-Rg+Bu) t)
    (hJ : inner ℝ g Jg = 0) (hport : inner ℝ g Bu = inner ℝ y u) :
    HasDerivAt (fun s => H (x s)) (-inner ℝ g Rg+inner ℝ y u) t := by
  convert hH.comp_hasDerivAt t hx using 1
  exact (power_balance g Jg Rg Bu u y hJ hport).symm

theorem passive_supply (g Jg Rg Bu : E) (u y : U)
    (hJ : inner ℝ g Jg = 0) (hR : 0 ≤ inner ℝ g Rg)
    (hport : inner ℝ g Bu = inner ℝ y u) :
    inner ℝ g (Jg-Rg+Bu) ≤ inner ℝ y u := by
  rw [power_balance g Jg Rg Bu u y hJ hport]
  linarith

/-- Power-conserving interconnection: exchanged supply cancels exactly.
This is the relevant structure behind the backstepping cross terms. -/
theorem interconnected_dissipation (dH₁ dH₂ loss₁ loss₂ supply : ℝ)
    (h₁ : dH₁ ≤ -loss₁+supply) (h₂ : dH₂ ≤ -loss₂-supply) :
    dH₁+dH₂ ≤ -(loss₁+loss₂) := by linarith

end GNC.PortHamiltonian
