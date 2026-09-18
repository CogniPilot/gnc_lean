import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Residual arithmetic that retains low homogeneous degrees and charges
all discarded products. The functions can be evaluated at any time and
uncertain parameter, so their bounds can retain complete time profiles.
This is shared algebra, independent of Cartesian or Lie coordinates. -/
namespace GNC.TruncatedProduct

/-- Propagate two existing enclosure errors and a checked core-product
truncation error. No product of errors is silently discarded. -/
theorem multiplication {x y p q z A B E F R : ℝ}
    (hp : |p|≤A) (hq : |q|≤B) (hx : |x-p|≤E) (hy : |y-q|≤F)
    (hz : |p*q-z|≤R) : |x*y-z|≤R+A*F+B*E+E*F := by
  have hA := (abs_nonneg _).trans hp
  have hB := (abs_nonneg _).trans hq
  have hE := (abs_nonneg _).trans hx
  have hF := (abs_nonneg _).trans hy
  have h1 : |p*(y-q)|≤A*F := by
    rw [abs_mul]
    exact mul_le_mul hp hy (abs_nonneg _) hA
  have h2 : |q*(x-p)|≤B*E := by
    rw [abs_mul]
    exact mul_le_mul hq hx (abs_nonneg _) hB
  have h3 : |(x-p)*(y-q)|≤E*F := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hE
  have hid : x*y-z=(p*q-z)+p*(y-q)+q*(x-p)+(x-p)*(y-q) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hz h1)) h2)) h3)

/-- Bound omitted homogeneous degree pairs before expanding their products.
This avoids computing high-degree coefficients only to bound them afterward.
Any exact decomposition into blocks is admissible; degrees need not be
distinct, and zero-degree terms and empty sums are included. -/
theorem discarded_pairs {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p A : ι → ℝ) (q B : κ → ℝ) (dp : ι → ℕ) (dq : κ → ℕ) (N : ℕ)
    (hp : ∀ i ∈ s, |p i|≤A i) (hq : ∀ j ∈ t, |q j|≤B j) :
    |(∑ i ∈ s, p i)*(∑ j ∈ t, q j)-
      ∑ i ∈ s, ∑ j ∈ t, if dp i+dq j≤N then p i*q j else 0|≤
      ∑ i ∈ s, ∑ j ∈ t, if dp i+dq j≤N then 0 else A i*B j := by
  classical
  have hid : (∑ i ∈ s, p i)*(∑ j ∈ t, q j)-
      (∑ i ∈ s, ∑ j ∈ t, if dp i+dq j≤N then p i*q j else 0)=
      ∑ i ∈ s, ∑ j ∈ t, if dp i+dq j≤N then 0 else p i*q j := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [hid]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · simp
  · rw [abs_mul]
    exact mul_le_mul (hp i hi) (hq j hj) (abs_nonneg _) ((abs_nonneg _).trans (hp i hi))

end GNC.TruncatedProduct
