import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic

/-! Frobenius bounds for Euclidean operators using their orthonormal columns.
This bridges an operator-norm truncation theorem and entrywise endpoint checks.
-/
noncomputable section
namespace GNC.EuclideanOperator

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Operator (n : ℕ) := Space n →L[ℝ] Space n

def columns {n : ℕ} (L : Operator n) : PiLp 2 (fun _ : Fin n => Space n) :=
  WithLp.toLp 2 (fun j => L (EuclideanSpace.single j 1))

def frobenius {n : ℕ} (L : Operator n) : ℝ := ‖columns L‖

theorem frobenius_sq {n : ℕ} (L : Operator n) :
    frobenius L^2 = ∑ j : Fin n, ∑ i : Fin n, (L (EuclideanSpace.single j 1) i)^2 := by
  rw [frobenius, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  exact EuclideanSpace.real_norm_sq_eq _

theorem columns_sub {n : ℕ} (L K : Operator n) : columns (L-K) = columns L-columns K := by
  ext j i
  rfl

theorem frobenius_triangle {n : ℕ} (L K H : Operator n) :
    frobenius (L-H) ≤ frobenius (L-K)+frobenius (K-H) := by
  unfold frobenius
  rw [columns_sub, columns_sub, columns_sub]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem frobenius_le_operator {n : ℕ} (L : Operator n) :
    frobenius L ≤ Real.sqrt n * ‖L‖ := by
  have hj (j : Fin n) : ‖columns L j‖ ≤ ‖L‖ := by
    simpa [columns] using L.le_opNorm (EuclideanSpace.single j (1 : ℝ))
  have hsq : frobenius L ^ 2 ≤ (n : ℝ)*‖L‖^2 := by
    rw [frobenius, PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ j : Fin n, ‖L‖^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hj j) 2
      _ = (n : ℝ)*‖L‖^2 := by simp
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hn : 0 ≤ frobenius L := norm_nonneg _
  have hsq' : frobenius L^2 ≤ (Real.sqrt n * ‖L‖)^2 := by
    rw [mul_pow, hs]
    exact hsq
  nlinarith only [hsq', hn, mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (norm_nonneg L)]

theorem reported_bound {n : ℕ} (L K H : Operator n) {δ ε : ℝ}
    (hδ : ‖L-K‖ ≤ δ) (hε : frobenius (K-H) ≤ ε) :
    frobenius (L-H) ≤ Real.sqrt n * δ + ε := by
  calc
    _ ≤ frobenius (L-K)+frobenius (K-H) := frobenius_triangle L K H
    _ ≤ Real.sqrt n * ‖L-K‖ + ε := add_le_add (frobenius_le_operator _) hε
    _ ≤ Real.sqrt n * δ + ε := by gcongr

/-- A squared entrywise budget justifies the finite-evaluation Frobenius
distance without any numerical square-root tolerance. -/
theorem frobenius_le_of_entry_bounds {n : ℕ} (L : Operator n)
    (e : Fin n → Fin n → ℝ) {ε : ℝ}
    (he : ∀ j i, |L (EuclideanSpace.single j 1) i| ≤ e j i)
    (hε : 0 ≤ ε) (hs : (∑ j : Fin n, ∑ i : Fin n, (e j i)^2) ≤ ε^2) :
    frobenius L ≤ ε := by
  have hsq : frobenius L^2 ≤ ε^2 := by
    rw [frobenius_sq]
    apply le_trans _ hs
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨hl, hu⟩ := abs_le.mp (he j i)
    have h := mul_nonneg (show 0 ≤ e j i + L (EuclideanSpace.single j 1) i by linarith)
      (show 0 ≤ e j i - L (EuclideanSpace.single j 1) i by linarith)
    nlinarith
  have hn : 0 ≤ frobenius L := norm_nonneg _
  nlinarith

end GNC.EuclideanOperator
