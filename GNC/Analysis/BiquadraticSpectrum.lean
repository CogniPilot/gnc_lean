import GNC.Analysis.BiquadraticExponential

/-! Constructing the simple exponential modes from the biquadratic relation.
This algebraic split is independent of a numerical eigenvalue solver. A zero
root requires a Jordan mode and is deliberately excluded from this split. -/
noncomputable section
set_option autoImplicit false
namespace GNC.BiquadraticSpectrum
open QuadraticModes
variable {A : Type*} [Ring A] [Algebra ℂ A]

def split (W E : A) (rate : ℂ) : A := (1/2 : ℂ) • (E+rate⁻¹ • (W*E))

theorem split_sum (W E : A) (rate : ℂ) :
    split W E rate + split W E (-rate) = E := by
  simp only [split, inv_neg]
  module

theorem split_eigen (W E : A) (rate : ℂ) (hrate : rate ≠ 0)
    (hE : W^2*E = rate^2 • E) : W*split W E rate = rate • split W E rate := by
  simp only [split, mul_smul_comm, mul_add, ← mul_assoc, ← pow_two, hE, smul_smul]
  have hr : rate⁻¹*rate^2 = rate := by field_simp
  rw [hr]
  simp only [smul_add, smul_smul]
  have hi : rate*(1/2)*rate⁻¹ = (1/2 : ℂ) := by field_simp
  rw [hi]
  module

/-- The two signed roots split a square-mode projector into eigenmodes. -/
theorem projector_eigen (W : A) (p q rate : ℂ)
    (hW : W^4 = (p+q) • W^2-(p*q) • (1 : A))
    (hrate : rate ≠ 0) (hsquare : rate^2 = p) :
    W*split W (projector W p q) rate = rate • split W (projector W p q) rate := by
  apply split_eigen W (projector W p q) rate hrate
  rw [hsquare]
  exact projector_square W p q hW

theorem four_modes_sum (W : A) (p q α β : ℂ) (hpq : p ≠ q) :
    split W (projector W p q) α + split W (projector W p q) (-α) +
      (split W (projector W q p) β + split W (projector W q p) (-β)) = 1 := by
  rw [split_sum, split_sum, projector_sum W p q hpq]

end GNC.BiquadraticSpectrum
