import GNC.Analysis.AffineProductCertificate

/-! Degreewise sums of products preserve cancellation in a scalar expression
before taking its range. Only discarded products are bounded separately. -/
namespace GNC.DegreeProductCertificate
open ParameterPolynomial BallPolynomialEnclosure

def sumProductDegree {m : ℕ} (d : ℕ) (p q : Fin m → Partition) : Coefficients :=
  polynomialSum fun i => degreeProduct d (p i) (q i)

noncomputable section

theorem checked_sumProduct_value {m : ℕ} (N : ℕ) (p q : Fin m → Partition)
    (base r : Fin (N+1) → Coefficients)
    (hr : ∀ d, zero (subtract (add (base d) (sumProductDegree d.val p q)) (r d)))
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble base) x t+(∑ i, value (retainedProduct N (p i) (q i)) x t)=
      value (assemble r) x t := by
  rw [assemble_value,assemble_value]
  simp_rw [retained_by_degree]
  rw [Finset.sum_comm,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simpa only [value_add,sumProductDegree,polynomialSum_value] using
    ParameterPolynomial.identity _ _ (hr d) x t

theorem sumProduct_error {m : ℕ} (N : ℕ) (p q : Fin m → Partition)
    (base r : Fin (N+1) → Coefficients)
    (hr : ∀ d, zero (subtract (add (base d) (sumProductDegree d.val p q)) (r d)))
    {σ : ℚ} (hp : ∀ i, (p i).Valid σ) (hq : ∀ i, (q i).Valid σ)
    {x : Fin 3 → ℝ} (hx : x 0^2+x 1^2+x 2^2≤(σ:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    |value (assemble base) x t+(∑ i, value (p i).core x t*value (q i).core x t)-
      value (assemble r) x t|≤
      PolynomialOrder.value (profileSum fun i => discardedProfile N (p i) (q i)) t := by
  rw [←checked_sumProduct_value N p q base r hr x t,profileSum_value]
  have he : value (assemble base) x t+(∑ i, value (p i).core x t*value (q i).core x t)-
      (value (assemble base) x t+(∑ i, value (retainedProduct N (p i) (q i)) x t))=
      ∑ i, (value (p i).core x t*value (q i).core x t-
        value (retainedProduct N (p i) (q i)) x t) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => truncation_bound N (p i) (q i) (hp i) (hq i) hx ht)

end
end GNC.DegreeProductCertificate
