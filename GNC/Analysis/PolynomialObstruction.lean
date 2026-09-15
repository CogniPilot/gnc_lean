import GNC.Planning.PolynomialKernel

/-! Finite witnesses for lower bounds on *every* polynomial of a given degree.
A signed combination of sample values annihilates all low-degree monomials.
Its nonzero value on a physical response then obstructs polynomial accuracy.
The argument permits independently certified errors at every sample and
does not assume that interpolation or a chosen fitting algorithm is optimal.
-/
namespace GNC.PolynomialObstruction
open Finset

variable {n d : ℕ}

/-- Zero moments annihilate every polynomial in the entire degree class. -/
theorem annihilates (x w : Fin n → ℝ)
    (hm : ∀ k ≤ d, ∑ i, w i * x i ^ k = 0)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d) :
    ∑ i, w i * p.eval (x i) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k ≤ d := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hp
  calc
    ∑ i, w i * (p.coeff k * x i ^ k) =
        p.coeff k * ∑ i, w i * x i ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hm k hk', mul_zero]

/-- Propagate certified sample errors through any finite signed witness. -/
theorem sample_error (w f a δ : Fin n → ℝ)
    (h : ∀ i, |f i-a i| ≤ δ i) :
    |(∑ i, w i*f i)-(∑ i, w i*a i)| ≤ ∑ i, |w i| *δ i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |w i*f i-w i*a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| *δ i := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

/-- Any uniform polynomial error budget must exceed the measured witness
amplitude minus its certified sample uncertainty. The weights have unit
total variation, so the sample uncertainty is not silently amplified. -/
theorem error_lower_bound (x w f a δ : Fin n → ℝ)
    (hm : ∀ k ≤ d, ∑ i, w i*x i^k = 0)
    (hw : ∑ i, |w i| = 1)
    (hf : ∀ i, |f i-a i| ≤ δ i)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d) {ε : ℝ}
    (he : ∀ i, |f i-p.eval (x i)| ≤ ε) :
    |∑ i, w i*a i| - ∑ i, |w i| *δ i ≤ ε := by
  have he' := sample_error w f (fun i => p.eval (x i)) (fun _ => ε) he
  rw [annihilates x w hm p hp, sub_zero, ← Finset.sum_mul, hw, one_mul] at he'
  have hf' := sample_error w f a δ hf
  have ht : |∑ i, w i*a i| ≤ |∑ i, w i*f i| +
      |(∑ i, w i*f i)-(∑ i, w i*a i)| := by
    have h := abs_sub_le (∑ i, w i*a i) (∑ i, w i*f i) 0
    simp only [sub_zero] at h
    rw [abs_sub_comm, add_comm] at h
    exact h
  linarith

/-- A finite, checkable obstruction supplies an actual bad point, rather
than just failure of a particular upper-bound computation. -/
theorem exists_error_gt (x w f a δ : Fin n → ℝ)
    (hm : ∀ k ≤ d, ∑ i, w i*x i^k = 0)
    (hw : ∑ i, |w i| = 1) (hf : ∀ i, |f i-a i| ≤ δ i)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d) {ε : ℝ}
    (hε : ε < |∑ i, w i*a i| - ∑ i, |w i| *δ i) :
    ∃ i, ε < |f i-p.eval (x i)| := by
  by_contra! h
  exact (error_lower_bound x w f a δ hm hw hf p hp h).not_gt hε

end GNC.PolynomialObstruction
