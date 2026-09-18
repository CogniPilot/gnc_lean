import GNC.Analysis.BallPolynomialEnclosure

/-! Check retained polynomial products one degree at a time. Reassembly is
by concatenation, so the final proof does not recompute the large merged
product. Every small product identity is still checked by the kernel. -/
namespace GNC.DegreeProductCertificate
open ParameterPolynomial BallPolynomialEnclosure

def degreeProduct (d : ℕ) (p q : Partition) : Coefficients :=
  polynomialSum fun i => polynomialSum fun j =>
    if (p.blocks i).degree+(q.blocks j).degree=d then
      multiply (p.blocks i).core (q.blocks j).core else []

def assemble {n : ℕ} (r : Fin n → Coefficients) : Coefficients :=
  (List.finRange n).flatMap r

noncomputable section

theorem degreeProduct_value (d : ℕ) (p q : Partition) (x : Fin 3 → ℝ) (t : ℝ) :
    value (degreeProduct d p q) x t=
      ∑ i, ∑ j, if (p.blocks i).degree+(q.blocks j).degree=d then
        value (p.blocks i).core x t*value (q.blocks j).core x t else 0 := by
  simp only [degreeProduct,polynomialSum_value]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [value_multiply]

theorem assemble_value {n : ℕ} (r : Fin n → Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    value (assemble r) x t=∑ i, value (r i) x t := by
  have hf (l : List (Fin n)) :
      value (l.flatMap r) x t=(l.map fun i => value (r i) x t).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.flatMap_cons,value,List.map_append,List.sum_append,
        List.map_cons,List.sum_cons] at *
      rw [ih]
  rw [assemble,hf]
  rw [←List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]

private theorem degree_sum (s N : ℕ) (v : ℝ) :
    (∑ d : Fin (N+1), if s=d.val then v else 0)=if s≤N then v else 0 := by
  classical
  by_cases h : s≤N
  · let k : Fin (N+1) := ⟨s,by omega⟩
    have he (d : Fin (N+1)) : s=d.val ↔ k=d := by
      change k.val=d.val ↔ k=d
      exact Fin.ext_iff.symm
    simp_rw [he]
    simp [h]
  · have he (d : Fin (N+1)) : ¬s=d.val := by have hd := d.isLt; omega
    simp [he,h]

theorem retained_by_degree (N : ℕ) (p q : Partition) (x : Fin 3 → ℝ) (t : ℝ) :
    value (retainedProduct N p q) x t=
      ∑ d : Fin (N+1), value (degreeProduct d.val p q) x t := by
  rw [retainedProduct_value]
  simp_rw [degreeProduct_value]
  calc
    _=∑ i, ∑ j, ∑ d : Fin (N+1),
        if (p.blocks i).degree+(q.blocks j).degree=d.val then
          value (p.blocks i).core x t*value (q.blocks j).core x t else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (degree_sum _ N _).symm
    _=∑ i, ∑ d : Fin (N+1), ∑ j,
        if (p.blocks i).degree+(q.blocks j).degree=d.val then
          value (p.blocks i).core x t*value (q.blocks j).core x t else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _=_ := Finset.sum_comm

/-- Kernel-checked degree pieces identify the entire retained product. -/
theorem checked_value (N : ℕ) (p q : Partition) (r : Fin (N+1) → Coefficients)
    (hr : ∀ d, zero (subtract (degreeProduct d.val p q) (r d)))
    (x : Fin 3 → ℝ) (t : ℝ) :
    value (retainedProduct N p q) x t=value (assemble r) x t := by
  rw [retained_by_degree,assemble_value]
  apply Finset.sum_congr rfl
  intro d _
  exact ParameterPolynomial.identity _ _ (hr d) x t

end
end GNC.DegreeProductCertificate
