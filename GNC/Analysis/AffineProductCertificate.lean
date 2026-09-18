import GNC.Analysis.DegreeProductCertificate

/-! Degreewise affine residual checks built on cached product identities. -/
namespace GNC.DegreeProductCertificate
open ParameterPolynomial BallPolynomialEnclosure
noncomputable section

/-- Check an affine residual by degree, so cancellation occurs before its
range is bounded. No merged rational product is recomputed at reassembly. -/
theorem checked_affine_value (N : ℕ) (p q : Partition) (K : ℚ)
    (base r : Fin (N+1) → Coefficients)
    (hr : ∀ d, zero (subtract
      (add (base d) (scale K (degreeProduct d.val p q))) (r d)))
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble base) x t+(K:ℝ)*value (retainedProduct N p q) x t=
      value (assemble r) x t := by
  rw [assemble_value,retained_by_degree,assemble_value,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simpa only [value_add,value_scale] using ParameterPolynomial.identity _ _ (hr d) x t

/-- Transfer the checked affine identity to its untruncated scalar product. -/
theorem affine_error (N : ℕ) (p q : Partition) (K : ℚ) (hK : 0≤K)
    (base r : Fin (N+1) → Coefficients)
    (hr : ∀ d, zero (subtract
      (add (base d) (scale K (degreeProduct d.val p q))) (r d)))
    {σ : ℚ} (hp : p.Valid σ) (hq : q.Valid σ)
    {x : Fin 3 → ℝ} (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    |value (assemble base) x t+(K:ℝ)*(value p.core x t*value q.core x t)-
      value (assemble r) x t|≤
      (K:ℝ)*PolynomialOrder.value (discardedProfile N p q) t := by
  rw [←checked_affine_value N p q K base r hr x t]
  have he : value (assemble base) x t+(K:ℝ)*(value p.core x t*value q.core x t)-
      (value (assemble base) x t+(K:ℝ)*value (retainedProduct N p q) x t)=
      (K:ℝ)*(value p.core x t*value q.core x t-value (retainedProduct N p q) x t) := by ring
  rw [he,abs_mul,abs_of_nonneg (show (0:ℝ)≤K by exact_mod_cast hK)]
  exact mul_le_mul_of_nonneg_left (truncation_bound N p q hp hq hx ht)
    (by exact_mod_cast hK)


end
end GNC.DegreeProductCertificate
