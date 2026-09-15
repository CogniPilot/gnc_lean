import GNC.Analysis.PolynomialIntegral

/-! Add certified integral pieces without assuming the polynomial pieces
agree at their endpoints. The actual continuous integrand supplies the
common integral; each approximation has its own explicit error allowance.
-/
namespace GNC.IntegralPartition
open scoped BigOperators

theorem error_sum (f : ℝ → ℝ) (times values errors : ℕ → ℝ) (n : ℕ)
    (hf : ∀ k < n, IntervalIntegrable f MeasureTheory.volume (times k) (times (k+1)))
    (he : ∀ k < n, |(∫ t in times k..times (k+1), f t)-values k| ≤ errors k) :
    |(∫ t in times 0..times n, f t) - ∑ k ∈ Finset.range n, values k| ≤
      ∑ k ∈ Finset.range n, errors k := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hf, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun k hk => he k (Finset.mem_range.mp hk)))

theorem length_sum (times : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (times (k+1)-times k)) = times n-times 0 := by
  exact Finset.sum_range_sub times n

theorem uniform_error (f : ℝ → ℝ) (times values : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hf : ∀ k < n, IntervalIntegrable f MeasureTheory.volume (times k) (times (k+1)))
    (he : ∀ k < n,
      |(∫ t in times k..times (k+1), f t)-values k| ≤ (times (k+1)-times k)*ε) :
    |(∫ t in times 0..times n, f t) - ∑ k ∈ Finset.range n, values k| ≤
      (times n-times 0)*ε := by
  have h := error_sum f times values (fun k => (times (k+1)-times k)*ε) n hf he
  rwa [← Finset.sum_mul, length_sum] at h

end GNC.IntegralPartition
