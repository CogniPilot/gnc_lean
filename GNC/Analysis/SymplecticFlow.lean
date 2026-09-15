import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-! Symplectic preservation from an actual matrix differential equation.
Derivatives are proved entrywise, so no submultiplicativity assumption is
made about the default elementwise matrix norm. The inverse formula reduces
validated inverse evaluation to a linear operation on the forward matrix.
-/
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise
namespace GNC.SymplecticFlow
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem transpose_derivative {F : ℝ → Matrix n n ℝ} {D : Matrix n n ℝ} {t : ℝ}
    (hF : HasDerivAt F D t) : HasDerivAt (fun s => (F s)ᵀ) Dᵀ t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hF j) i

theorem mul_derivative {F H : ℝ → Matrix n n ℝ} {D E : Matrix n n ℝ} {t : ℝ}
    (hF : HasDerivAt F D t) (hH : HasDerivAt H E t) :
    HasDerivAt (fun s => F s * H s) (D * H t + F t * E) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hF i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hH k) j))
  convert h using 1 <;> simp [Matrix.mul_apply, Finset.sum_add_distrib]
  funext x
  simp

theorem form_derivative {F : ℝ → Matrix n n ℝ} {A J : Matrix n n ℝ} {t : ℝ}
    (hF : HasDerivAt F (A * F t) t) (hA : Aᵀ * J + J * A = 0) :
    HasDerivAt (fun s => (F s)ᵀ * J * F s) 0 t := by
  have h := mul_derivative (mul_derivative (transpose_derivative hF) (hasDerivAt_const t J)) hF
  convert h using 1
  simp only [Matrix.transpose_mul, Matrix.mul_zero, add_zero]
  symm
  calc
    _ = (F t)ᵀ * (Aᵀ * J + J * A) * F t := by noncomm_ring
    _ = 0 := by rw [hA]; simp

/-- Conservation of the bilinear form on a finite interval, derived from
the matrix ODE rather than postulated for the numerical transition. -/
theorem preserves_form (F A : ℝ → Matrix n n ℝ) (J : Matrix n n ℝ) {T : ℝ}
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A t * F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) T, (A t)ᵀ * J + J * A t = 0)
    (hi : F 0 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) T, (F t)ᵀ * J * F t = J := by
  intro t ht
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => (form_derivative (hd u ⟨hu.1,hu.2.trans ht.2⟩)
      (hA u ⟨hu.1,hu.2.trans ht.2⟩)).hasDerivWithinAt)
    (fun _ _ => show ‖(0:Matrix n n ℝ)‖ ≤ 0 by simp)
    t (Set.right_mem_Icc.mpr ht.1)
  simp only [zero_mul] at hm
  have hz := norm_eq_zero.mp (le_antisymm hm (norm_nonneg _))
  simpa [hi] using sub_eq_zero.mp hz

/-- General fixed-coordinate form of the symplectic inverse formula. The
matrix inverse is mathlib's nonsingular inverse, justified by a left inverse. -/
theorem inverse_of_preserved (F J : Matrix n n ℝ) (hJ : J * J = -1)
    (hF : Fᵀ * J * F = J) : F⁻¹ = (-J) * Fᵀ * J := by
  apply Matrix.inv_eq_left_inv
  calc
    (-J) * Fᵀ * J * F = (-J) * (Fᵀ * J * F) := by noncomm_ring
    _ = 1 := by
      rw [hF, Matrix.neg_mul, hJ]
      ext i j
      simp

/-- Reuse mathlib's symplectic-group interface for canonical sum indices. -/
theorem mem_symplectic {l : Type*} [Fintype l] [DecidableEq l]
    (F A : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) {T : ℝ}
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (A t * F t) t)
    (hA : ∀ t ∈ Set.Icc (0:ℝ) T,
      (A t)ᵀ * Matrix.J l ℝ + Matrix.J l ℝ * A t = 0)
    (hi : F 0 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) T, F t ∈ Matrix.symplecticGroup l ℝ := by
  intro t ht
  exact SymplecticGroup.mem_iff'.mpr (preserves_form F A (Matrix.J l ℝ) hd hA hi t ht)

end GNC.SymplecticFlow
