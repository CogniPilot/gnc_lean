import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-! The characteristic polynomial of the constant rotating gravity-gradient
equations, allowing independent gravity strength and reference angular rate.
Cayley–Hamilton is applied from mathlib, not reproved here. -/
noncomputable section
namespace GNC.RotatingGravity
open Matrix Polynomial
open scoped Matrix

/-- State order is radial position, along-track position, and their derivatives. -/
def planar (k w : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1, 0; 0, 0, 0, 1;
     2*k+w^2, 0, 0, 2*w; 0, w^2-k, -2*w, 0]

def normal (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -k, 0]

theorem planar_charpoly (k w : ℝ) :
    (planar k w).charpoly = X^4 + C (2*w^2-k)*X^2 + C ((w^2-k)*(w^2+2*k)) := by
  rw [Matrix.charpoly, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, charmatrix_apply, diagonal_apply, planar,
    submatrix_apply, Fin.succAbove]
  rw [Polynomial.C_ofNat]
  ring

theorem normal_charpoly (k : ℝ) : (normal k).charpoly = X^2 + C k := by
  simp [Matrix.charpoly, det_fin_two, normal]
  ring

/-- All higher planar powers reduce to four basis matrices. -/
theorem planar_relation (k w : ℝ) :
    planar k w ^ 4 + (2*w^2-k) • planar k w ^ 2 +
      ((w^2-k)*(w^2+2*k)) • (1 : Matrix (Fin 4) (Fin 4) ℝ) = 0 := by
  have h := Matrix.aeval_self_charpoly (planar k w)
  rw [planar_charpoly] at h
  simpa [Algebra.smul_def] using h

theorem normal_relation (k : ℝ) : normal k ^ 2 = (-k) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h := Matrix.aeval_self_charpoly (normal k)
  rw [normal_charpoly] at h
  have he : normal k ^ 2 + k • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    simpa [Algebra.smul_def] using h
  simpa using eq_neg_of_add_eq_zero_left he

end GNC.RotatingGravity
