import GNC.Analysis.PolynomialIntegral

/-! Exact bookkeeping for finite switched integrals. Clipping every interval
at a query time equals the completed intervals and one partial interval.
No numerical integration or differentiability at switches is required.
-/
namespace GNC.IntegralPrefix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clipped_sum (f : ℕ → ℝ → E) (nodes : ℕ → ℝ) {N n : ℕ} {T : ℝ}
    (hn : n < N) (ho : Monotone nodes) (ht : nodes n ≤ T ∧ T ≤ nodes (n+1)) :
    (∑ k ∈ Finset.range N, ∫ t in min (nodes k) T..min (nodes (k+1)) T, f k t) =
      (∑ k ∈ Finset.range n, ∫ t in nodes k..nodes (k+1), f k t)+
        ∫ t in nodes n..T, f n t := by
  let g := fun k => ∫ t in min (nodes k) T..min (nodes (k+1)) T, f k t
  have hf (k : ℕ) (hk : n+1 ≤ k) : g k = 0 := by
    have h1 : T ≤ nodes k := ht.2.trans (ho hk)
    have h2 : T ≤ nodes (k+1) := ht.2.trans (ho (by omega))
    simp only [g,min_eq_right h1,min_eq_right h2,intervalIntegral.integral_same]
  have he : (∑ k ∈ Finset.range (n+1), g k) = ∑ k ∈ Finset.range N, g k := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _hk hk
    exact hf k (by simpa only [Finset.mem_range,not_lt] using hk)
  change (∑ k ∈ Finset.range N, g k) = _
  rw [← he,Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have h1 : nodes k ≤ T := (ho (by have := Finset.mem_range.mp hk; omega)).trans ht.1
    have h2 : nodes (k+1) ≤ T := (ho (by have := Finset.mem_range.mp hk; omega)).trans ht.1
    simp only [g,min_eq_left h1,min_eq_left h2]
  · simp only [g,min_eq_left ht.1,min_eq_right ht.2]

/-- A common primitive makes an exact partition-refinement certificate
independent of the particular integrand. -/
theorem integral_primitive_difference (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    (∫ t in a..b, f t) = (∫ t in (0:ℝ)..b, f t)-(∫ t in (0:ℝ)..a, f t) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := MeasureTheory.volume) (0:ℝ) a)
    (hf.intervalIntegrable (μ := MeasureTheory.volume) a b)
  rw [← h]
  abel

end GNC.IntegralPrefix
