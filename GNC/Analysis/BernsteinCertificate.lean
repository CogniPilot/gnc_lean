import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Tensor-product Bernstein range certificates, as used by validated Taylor
model range bounders. Mathlib supplies positivity and the partition of unity.
Any number of parameters, including zero, and any per-parameter degree are
allowed. Conversion to Bernstein coefficients and their rounding bounds are
separate obligations; this does not audit audi's matrix conversion algorithm.
-/
noncomputable section
open scoped BigOperators unitInterval
namespace GNC.BernsteinCertificate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weight (n : ι → ℕ) (k : ∀ j, Fin (n j+1)) (x : ι → I) : ℝ :=
  ∏ j, bernstein (n j) (k j) (x j)

omit [DecidableEq ι] in
theorem weight_nonneg (n : ι → ℕ) (k : ∀ j, Fin (n j+1)) (x : ι → I) :
    0 ≤ weight n k x := Finset.prod_nonneg (fun _ _ => bernstein_nonneg)

theorem partition (n : ι → ℕ) (x : ι → I) :
    (∑ k : ∀ j, Fin (n j+1), weight n k x) = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun j (k : Fin (n j+1)) => bernstein (n j) k (x j))]
  simp

def evaluate (n : ι → ℕ) (b : (∀ j, Fin (n j+1)) → ℝ) (x : ι → I) : ℝ :=
  ∑ k, weight n k x*b k

/-- A finite set of coefficient inequalities certifies every point in the
parameter box. This includes all cross terms, not just sampled vertices. -/
theorem range_bound (n : ι → ℕ) (b : (∀ j, Fin (n j+1)) → ℝ)
    (x : ι → I) {lo hi : ℝ} (hb : ∀ k, lo ≤ b k ∧ b k ≤ hi) :
    lo ≤ evaluate n b x ∧ evaluate n b x ≤ hi := by
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_left (hb k).1 (weight_nonneg n k x))
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_left (hb k).2 (weight_nonneg n k x))
  rw [← Finset.sum_mul, partition, one_mul] at hlo
  rw [← Finset.sum_mul, partition, one_mul] at hhi
  exact ⟨hlo,hhi⟩

/-- Independent coefficient-rounding errors are bounded without multiplying
the largest error by the number of coefficients: weights sum to one. -/
theorem coefficient_error (n : ι → ℕ) (b approx : (∀ j, Fin (n j+1)) → ℝ)
    (x : ι → I) {ε : ℝ} (hb : ∀ k, |b k-approx k| ≤ ε) :
    |evaluate n b x-evaluate n approx x| ≤ ε := by
  have he : evaluate n b x-evaluate n approx x =
      evaluate n (fun k => b k-approx k) x := by
    simp only [evaluate, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  exact abs_le.mpr (range_bound n _ x (fun k => abs_le.mp (hb k)))

end GNC.BernsteinCertificate
