import GNC.Analysis.DegreeVectorCertificate

/-! Exact products assembled from separately checked degree pieces.
The degree labels only organize the finite partition; the range predicates
are not used because no product is discarded. -/
namespace GNC.ExactDegreeProduct
open ParameterPolynomial BallPolynomialEnclosure DegreeProductCertificate

def partition {n : ℕ} (p : Fin n → Coefficients) : Partition where
  count := n
  blocks i := ⟨i.val,p i,{ count := 0, terms := ![] }⟩

noncomputable section

theorem partition_value {n : ℕ} (p : Fin n → Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (partition p).core x t=value (assemble p) x t := by
  rw [Partition.core,polynomialSum_value,assemble_value]
  rfl

theorem product_value (N : ℕ) (p q : Partition)
    (h : ∀ i j, (p.blocks i).degree+(q.blocks j).degree≤N)
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (retainedProduct N p q) x t=value p.core x t*value q.core x t := by
  rw [retainedProduct_value,Partition.core,Partition.core,polynomialSum_value,polynomialSum_value]
  simp only [h,ite_true,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem checked_product (N : ℕ) (p q : Partition)
    (h : ∀ i j, (p.blocks i).degree+(q.blocks j).degree≤N)
    (r : Fin (N+1) → Coefficients)
    (hr : ∀ d, zero (subtract (degreeProduct d.val p q) (r d)))
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble r) x t=value p.core x t*value q.core x t := by
  rw [←checked_value N p q r hr,product_value N p q h]

theorem checked_affine (N : ℕ) (p q : Partition) (K : ℚ)
    (h : ∀ i j, (p.blocks i).degree+(q.blocks j).degree≤N)
    (base r : Fin (N+1) → Coefficients)
    (hr : ∀ d, zero (subtract
      (add (base d) (scale K (degreeProduct d.val p q))) (r d)))
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble r) x t=value (assemble base) x t+(K:ℝ)*value p.core x t*value q.core x t := by
  rw [←checked_affine_value N p q K base r hr,product_value N p q h]
  ring

end
end GNC.ExactDegreeProduct
