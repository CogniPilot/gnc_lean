import GNC.Dynamics.PlanarGravityVariation
import GNC.Analysis.SymplecticFlow

/-! Inverse solar gravity transitions from the checked symplectic identity.
The map is a signed permutation of entries, preserving componentwise error.
-/
noncomputable section
namespace GNC.PolynomialOrbitTransition
open scoped Matrix

def planeForm : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,0,-1,0; 0,0,0,-1; 1,0,0,0; 0,1,0,0]
def normalForm : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1; 1,0]

theorem planeForm_sq : planeForm * planeForm = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [planeForm, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem normalForm_sq : normalForm * normalForm = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalForm, Matrix.mul_apply, Fin.sum_univ_succ]

theorem plane_hamiltonian (z : Fin 5 → ℝ) :
    (planeGenerator z)ᵀ * planeForm + planeForm * planeGenerator z = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeGenerator, planeForm, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

theorem normal_hamiltonian (z : Fin 5 → ℝ) :
    (normalGenerator z)ᵀ * normalForm + normalForm * normalGenerator z = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalGenerator, normalForm, Matrix.mul_apply, Fin.sum_univ_succ]

def planeInverse (F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (-planeForm) * Fᵀ * planeForm
def normalInverse (H : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (-normalForm) * Hᵀ * normalForm

theorem plane_inverse (z : ℝ → Fin 5 → ℝ) (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) {T : ℝ}
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt F (planeGenerator (z t) * F t) t)
    (hi : F 0 = 1) : ∀ t ∈ Set.Icc (0:ℝ) T, (F t)⁻¹ = planeInverse (F t) := by
  intro t ht
  exact SymplecticFlow.inverse_of_preserved (F t) planeForm planeForm_sq
    (SymplecticFlow.preserves_form F (fun s => planeGenerator (z s)) planeForm hd
      (fun s _ => plane_hamiltonian (z s)) hi t ht)

theorem normal_inverse (z : ℝ → Fin 5 → ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {T : ℝ}
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt H (normalGenerator (z t) * H t) t)
    (hi : H 0 = 1) : ∀ t ∈ Set.Icc (0:ℝ) T, (H t)⁻¹ = normalInverse (H t) := by
  intro t ht
  exact SymplecticFlow.inverse_of_preserved (H t) normalForm normalForm_sq
    (SymplecticFlow.preserves_form H (fun s => normalGenerator (z s)) normalForm hd
      (fun s _ => normal_hamiltonian (z s)) hi t ht)

theorem planeInverse_sub (F P : Matrix (Fin 4) (Fin 4) ℝ) :
    planeInverse (F-P) = planeInverse F-planeInverse P := by
  simp only [planeInverse, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem normalInverse_sub (H P : Matrix (Fin 2) (Fin 2) ℝ) :
    normalInverse (H-P) = normalInverse H-normalInverse P := by
  simp only [normalInverse, Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem planeInverse_error (F P : Matrix (Fin 4) (Fin 4) ℝ) {ε : ℝ}
    (h : ∀ i j, |F i j-P i j| < ε) :
    ∀ i j, |planeInverse F i j-planeInverse P i j| < ε := by
  intro i j
  change |(planeInverse F-planeInverse P) i j| < ε
  rw [← planeInverse_sub]
  fin_cases i <;> fin_cases j <;>
    simp [planeInverse, planeForm, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecMul, dotProduct,
      abs_sub_comm] <;> exact h _ _

theorem normalInverse_error (H P : Matrix (Fin 2) (Fin 2) ℝ) {ε : ℝ}
    (h : ∀ i j, |H i j-P i j| < ε) :
    ∀ i j, |normalInverse H i j-normalInverse P i j| < ε := by
  intro i j
  change |(normalInverse H-normalInverse P) i j| < ε
  rw [← normalInverse_sub]
  fin_cases i <;> fin_cases j <;>
    simp [normalInverse, normalForm, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecMul, dotProduct, abs_sub_comm] <;> exact h _ _

end GNC.PolynomialOrbitTransition
