import GNC.Analysis.OscillatoryPolynomial

/-! Removing a constant diagonal rotation from the actual FOH equation.
Canonical FOH spinor kinematics is a 2×2 instance. The transformed generator
has finite polynomial/sine/cosine entries, so every finite ordered coefficient
has an elementary representation. No finite sum of all orders is asserted.
-/
noncomputable section
namespace GNC.Magnus
open GNC.Oscillatory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fohDiagonalGenerator (σ : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => Complex.I * (σ i : ℂ))

def fohRemoveDiagonal (σ : ι → ℝ) (U : ℝ → Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  fun i j => U t i j * mode (-σ j) t

def fohInteractionGenerator (σ : ι → ℝ) (B : ℝ → Matrix ι ι ℂ)
    (t : ℝ) : Matrix ι ι ℂ :=
  fun i j => mode (σ i) t * B t i j * mode (-σ j) t

theorem foh_mode_inverse (σ t : ℝ) : mode (-σ) t * mode σ t = 1 := by
  rw [← mode_add]
  simp [mode]

theorem foh_interaction_mul (σ : ι → ℝ) (U B : ℝ → Matrix ι ι ℂ) (t : ℝ) (i j : ι) :
    (fohRemoveDiagonal σ U t * fohInteractionGenerator σ B t) i j =
      (U t * B t) i j * mode (-σ j) t := by
  simp only [Matrix.mul_apply, fohRemoveDiagonal, fohInteractionGenerator, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (mode (-σ k) t * mode (σ k) t) *
        (U t i k * B t k j * mode (-σ j) t) := by ring
    _ = _ := by rw [foh_mode_inverse, one_mul]

/-- The actual ODE, after the change of variables, contains only the slope.
The conclusion is a time derivative of the given solution, not an assumed
interaction-picture model. -/
theorem foh_removeDiagonal_hasDerivAt (σ : ι → ℝ)
    (U B : ℝ → Matrix ι ι ℂ) (e t : ℝ)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j)
      ((U t * (fohDiagonalGenerator σ + (e : ℂ) • B t)) i j) t) (i j : ι) :
    HasDerivAt (fun t => fohRemoveDiagonal σ U t i j)
      ((e : ℂ) * (fohRemoveDiagonal σ U t * fohInteractionGenerator σ B t) i j) t := by
  have h := (hU i j).mul (mode_hasDerivAt (-σ j) t)
  convert h using 1
  rw [foh_interaction_mul]
  simp only [Matrix.mul_add, Matrix.add_apply, fohDiagonalGenerator,
    Matrix.mul_diagonal, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg]
  ring

/-- The initial condition is preserved at t=0. -/
theorem foh_removeDiagonal_initial (σ : ι → ℝ) (U : ℝ → Matrix ι ι ℂ)
    (hU : U 0 = 1) : fohRemoveDiagonal σ U 0 = 1 := by
  ext i j
  simp [fohRemoveDiagonal, hU, mode]

theorem foh_interaction_polynomial (σ : ι → ℝ) (B : ℝ → Matrix ι ι ℂ)
    (hB : ∀ i j, Oscillatory.Polynomial (fun t => B t i j)) (i j : ι) :
    Oscillatory.Polynomial (fun t => fohInteractionGenerator σ B t i j) := by
  have hleft : Oscillatory.Polynomial (mode (σ i)) := by
    simpa using Oscillatory.Polynomial.term 1 (σ i) 0
  have hright : Oscillatory.Polynomial (mode (-σ j)) := by
    simpa using Oscillatory.Polynomial.term 1 (-σ j) 0
  exact (hleft.mul (hB i j)).mul hright

/-- Centered affine slope, including the two-component FOH rotation generator. -/
def fohCenteredSlope (S : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  fun i j => ((t : ℂ) - 1/2) * S i j

theorem foh_centeredSlope_polynomial (S : Matrix ι ι ℂ) (i j : ι) :
    Oscillatory.Polynomial (fun t => fohCenteredSlope S t i j) := by
  have ht : Oscillatory.Polynomial (fun t : ℝ => (t : ℂ)) := by
    simpa [mode] using Oscillatory.Polynomial.term 1 0 1
  exact (ht.sub (Oscillatory.Polynomial.constant (1/2))).mul
    (Oscillatory.Polynomial.constant (S i j))

/-- Every finite FOH interaction coefficient is elementary after exact mean
rotation removal. This holds for every order, not just the audited degree 15. -/
theorem foh_all_finite_interaction_coefficients_elementary
    (σ : ι → ℝ) (S : Matrix ι ι ℂ) (n : ℕ) (i j : ι) :
    Oscillatory.Polynomial (fun t =>
      dysonCoefficient (fohInteractionGenerator σ (fohCenteredSlope S)) 0 n t i j) :=
  dysonCoefficient_polynomial _ 0
    (foh_interaction_polynomial σ _ (foh_centeredSlope_polynomial S)) n i j

end GNC.Magnus
