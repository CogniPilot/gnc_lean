import GNC.Lie.Jacobian
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! The singular-value statement of Lemma 2, using mathlib's adjoint,
eigenspaces and singular values on Euclidean space. -/
noncomputable section
open Matrix Real Module.End
open scoped Matrix RealInnerProductSpace
namespace GNC.Jacobian

theorem inner_ofLp (u v : E3) : inner ℝ u v = WithLp.ofLp u ⬝ᵥ WithLp.ofLp v := by
  rw [PiLp.inner_apply]
  change ∑ i : Fin 3, WithLp.ofLp v i*WithLp.ofLp u i =
    ∑ i : Fin 3, WithLp.ofLp u i*WithLp.ofLp v i
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem plane_adjoint (k : Vec3) (a b : ℝ) :
    (planeLinear k a b).adjoint = planeLinear k a (-b) := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [inner_ofLp]
  change planeMap k a (-b) (WithLp.ofLp u) ⬝ᵥ WithLp.ofLp v =
    WithLp.ofLp u ⬝ᵥ planeMap k a b (WithLp.ofLp v)
  simp only [planeMap, Axis.axial, Axis.transverse, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (WithLp.ofLp u) k]
  have hc : (k ⨯₃ WithLp.ofLp u) ⬝ᵥ WithLp.ofLp v =
      -(WithLp.ofLp u ⬝ᵥ (k ⨯₃ WithLp.ofLp v)) := by
    simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
  rw [hc]
  ring

def gram (k : Vec3) (a b : ℝ) : E3 →ₗ[ℝ] E3 :=
  (planeLinear k a b).adjoint.comp (planeLinear k a b)

theorem gram_apply (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) (v : E3) :
    WithLp.ofLp (gram k a b v) =
      (a^2+b^2) • WithLp.ofLp v+(1-(a^2+b^2)) • Axis.axial k (WithLp.ofLp v) := by
  rw [gram, plane_adjoint]
  change planeMap k a (-b) (planeMap k a b (WithLp.ofLp v)) = _
  rw [planeMap_comp k _ hk]
  simp [planeMap, Axis.transverse, pow_two]
  module

theorem gram_axis (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    gram k a b (WithLp.toLp 2 k) = WithLp.toLp 2 k := by
  apply (WithLp.linearEquiv 2 ℝ Vec3).injective
  change WithLp.ofLp (gram k a b (WithLp.toLp 2 k)) = k
  rw [gram_apply k hk]
  simp [Axis.axial, hk]

theorem gram_eigenvalue (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b μ : ℝ)
    (hμ : HasEigenvalue (gram k a b) μ) : μ = 1 ∨ μ = a^2+b^2 := by
  obtain ⟨v,hv,hv0⟩ := hμ.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv
  have h := congrArg WithLp.ofLp hv
  rw [gram_apply k hk] at h
  have ha := congrArg (fun w : Vec3 => k ⬝ᵥ w) h
  simp [Axis.axial, hk, dotProduct_add, dotProduct_smul] at ha
  by_cases h1 : μ = 1
  · exact Or.inl h1
  right
  have hd : k ⬝ᵥ WithLp.ofLp v = 0 := by
    have hm : (1-μ)*(k ⬝ᵥ WithLp.ofLp v) = 0 := by nlinarith only [ha]
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr (Ne.symm h1))
  simp only [Axis.axial, hd, zero_smul, smul_zero, add_zero] at h
  have he : (a^2+b^2-μ) • WithLp.ofLp v = 0 := by
    rw [sub_smul, h]; simp
  rcases smul_eq_zero.mp he with hc | hc
  · linarith
  · exact False.elim (hv0 ((WithLp.linearEquiv 2 ℝ Vec3).injective hc))

theorem gram_eigenspace_one (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) (hc : a^2+b^2 ≠ 1) :
    eigenspace (gram k a b) 1 = Submodule.span ℝ {WithLp.toLp 2 k} := by
  apply le_antisymm
  · intro v hv
    rw [mem_eigenspace_iff, one_smul] at hv
    have h := congrArg WithLp.ofLp hv
    rw [gram_apply k hk] at h
    have hz : (a^2+b^2-1) • (WithLp.ofLp v-Axis.axial k (WithLp.ofLp v)) = 0 := by
      linear_combination (norm := module) h
    have he := (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨k ⬝ᵥ WithLp.ofLp v, ?_⟩
    apply (WithLp.linearEquiv 2 ℝ Vec3).injective
    exact (sub_eq_zero.mp he).symm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    change WithLp.toLp 2 k ∈ eigenspace (gram k a b) 1
    rw [mem_eigenspace_iff, one_smul]
    exact gram_axis k hk a b

theorem axis_ne_zero (k : Vec3) (hk : k ⬝ᵥ k = 1) : (WithLp.toLp 2 k : E3) ≠ 0 := by
  intro h
  have hk0 : k = 0 := congrArg WithLp.ofLp h
  simp [hk0] at hk

theorem gram_hasEigenvalue_one (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) :
    HasEigenvalue (gram k a b) 1 := by
  apply hasEigenvalue_of_hasEigenvector (x := WithLp.toLp 2 k)
  refine ⟨?_, axis_ne_zero k hk⟩
  rw [mem_eigenspace_iff, one_smul]
  exact gram_axis k hk a b

theorem gram_one_multiplicity (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) (hc : a^2+b^2 ≠ 1) :
    Module.finrank ℝ (eigenspace (gram k a b) 1) = 1 := by
  rw [gram_eigenspace_one k hk a b hc]
  exact finrank_span_singleton (axis_ne_zero k hk)

private theorem sorted_three (f : Fin 3 → ℝ) (c : ℝ) (hc : c < 1)
    (hv : ∀ i, f i = 1 ∨ f i = c) (hm : Antitone f)
    (hn : Finset.card {i | f i = 1} = 1) : f = ![1,c,c] := by
  classical
  have h01 := hm (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := hm (show (1 : Fin 3) ≤ 2 by decide)
  rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1 <;> rcases hv 2 with h2 | h2
  all_goals try (exfalso; linarith only [h01,h12,hc,h0,h1,h2])
  all_goals norm_num [Fin.card_filter_univ_succ, h0, h1, h2, hc.ne] at hn
  all_goals try solve | funext i; fin_cases i <;> simp_all
  have hall : f = fun _ => c := funext (fun i => by fin_cases i <;> assumption)
  simp [hall, hc.ne] at hn

theorem gram_eigenvalues (k : Vec3) (hk : k ⬝ᵥ k = 1) (a b : ℝ) (hc : a^2+b^2 < 1) :
    (planeLinear k a b).isSymmetric_adjoint_comp_self.eigenvalues
      (by simp [E3] : Module.finrank ℝ E3 = 3) = ![1,a^2+b^2,a^2+b^2] := by
  apply sorted_three _ _ hc
  · intro i
    exact gram_eigenvalue k hk a b _
      ((planeLinear k a b).isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues _ i)
  · exact (planeLinear k a b).isSymmetric_adjoint_comp_self.eigenvalues_antitone _
  · have h := (planeLinear k a b).isSymmetric_adjoint_comp_self.card_filter_eigenvalues_eq
      (by simp [E3] : Module.finrank ℝ E3 = 3) (1 : ℝ)
    simpa using h.trans (gram_one_multiplicity k hk a b hc.ne)

theorem contraction_lt_one (t : ℝ) (ht : 0 < t) : contraction t < 1 := by
  apply (div_lt_one ht).mpr
  have h := sin_lt (show 0 < t/2 by linarith)
  linarith

/-- Equation (14), using mathlib's sorted singular values, not a separate
list assigned to the Jacobian by definition. -/
theorem left_singularValues (k : Vec3) (hk : k ⬝ᵥ k = 1) (t : ℝ)
    (ht : 0 < t) (htπ : t < 2*Real.pi) (i : Fin 3) :
    (leftCLM k t).toLinearMap.singularValues i = (![1,contraction t,contraction t] : Vec3) i := by
  have hc := contraction_pos t ht htπ
  have hc1 := contraction_lt_one t ht
  have hcoef : (sin t/t)^2+((1-cos t)/t)^2 < 1 := by
    rw [coefficients_sq]
    nlinarith
  rw [(leftCLM k t).toLinearMap.singularValues_fin (by simp [E3] : Module.finrank ℝ E3 = 3) i]
  change √((planeLinear k (sin t/t) ((1-cos t)/t)).isSymmetric_adjoint_comp_self.eigenvalues
      (by simp [E3] : Module.finrank ℝ E3 = 3) i) = _
  rw [gram_eigenvalues k hk _ _ hcoef, coefficients_sq]
  fin_cases i <;> simp [Real.sqrt_sq hc.le]

theorem left_singularValues_after_three (k : Vec3) (t : ℝ) (i : ℕ) (hi : 3 ≤ i) :
    (leftCLM k t).toLinearMap.singularValues i = 0 := by
  apply LinearMap.singularValues_of_finrank_le
  simpa [E3] using hi

end GNC.Jacobian
