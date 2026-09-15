import GNC.Estimation.GroupAffine
import GNC.Magnus.MagnusFlow
import GNC.Analysis.MixedFlow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform

/-! Exact log-linearity for ambient mixed-invariant matrix dynamics.

The coefficients are arbitrary elements of the ambient real Banach algebra:
they need not be invertible or belong to the state group's Lie algebra.
Subgroup tangency and the logarithm's chart domain are recorded separately.
This is the mixed-invariant class, not a representation theorem asserting
that every group-affine vector field has this ambient form.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NormedSpace Set Filter
open scoped Topology
namespace GNC.MixedInvariant
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def field (M N X : A) : A := M*X+X*N

theorem field_group_affine (M N : A) : Estimation.GroupAffine (field M N) := by
  intro X Y
  simp only [field, Units.val_mul, mul_one, one_mul]
  noncomm_ring

theorem field_group_affine_on (G : Subgroup Aˣ) (M N : A) :
    Estimation.GroupAffineOn G (field M N) :=
  fun X _ Y _ => field_group_affine M N X Y

/-- State-dependent coefficients may be introduced without changing
the vector field. Dependence of a chosen factorization is not intrinsic. -/
theorem field_gauge (X : Aˣ) (M N B : A) :
    field (M+X.val*B*(X⁻¹).val) (N-B) X.val = field M N X.val := by
  simp only [field, add_mul, mul_sub, mul_assoc, Units.inv_mul, mul_one]
  noncomm_ring

/-- Left trivialization of the actual vector field. The individual
summands need not be tangent. -/
theorem trivialized_field (X : Aˣ) (M N : A) :
    (X⁻¹).val * field M N X.val = (X⁻¹).val*M*X.val+N := by
  simp only [field, mul_add, ← mul_assoc, Units.inv_mul, one_mul]

def TangentOn (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A) (M N : A) : Prop :=
  ∀ X ∈ G, (X⁻¹).val*M*X.val+N ∈ 𝔤

theorem tangent_at_identity (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A)
    {M N : A} (h : TangentOn G 𝔤 M N) : M+N ∈ 𝔤 := by
  simpa using h 1 G.one_mem

/-- Tangency of the sum implies that conjugating M changes it only by
a Lie-algebra element, even when M itself is outside the Lie algebra. -/
theorem tangent_conjugate_difference (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A)
    {M N : A} (h : TangentOn G 𝔤 M N) (X : Aˣ) (hX : X ∈ G) :
    (X⁻¹).val*M*X.val-M ∈ 𝔤 := by
  convert 𝔤.sub_mem (h X hX) (tangent_at_identity G 𝔤 h) using 1 <;> abel

/-- The matrix exponential with its inverse, viewed in the ambient
unit group. This does not assert membership in the state subgroup. -/
def expUnit (Z : A) : Aˣ :=
  ⟨exp Z, exp (-Z), exp_cancel Z, exp_cancel' Z⟩

@[simp] theorem expUnit_val (Z : A) : (expUnit Z).val = exp Z := rfl

/-- Derivatives of curves in a closed linear subspace remain in it.
Finite-dimensional matrix Lie algebras have this closedness property. -/
theorem derivative_mem_submodule (𝔤 : Submodule ℝ A) (hg : IsClosed (𝔤 : Set A))
    {F : ℝ → A} {v : A} {t : ℝ} (hF : HasDerivAt F v t)
    (hm : ∀ s, F s ∈ 𝔤) : v ∈ 𝔤 := by
  apply hg.mem_of_tendsto hF.tendsto_slope
  exact Filter.Eventually.of_forall fun s =>
    𝔤.smul_mem ((s-t)⁻¹) (𝔤.sub_mem (hm s) (hm t))

/-- Tangency on G, together with exp(𝔤) ⊆ G, forces the right-error
linear generator to preserve 𝔤. Individual coefficient membership is
not assumed. -/
theorem tangent_commutator_mem (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A)
    (hg : IsClosed (𝔤 : Set A))
    (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    {M N Z : A} (h : TangentOn G 𝔤 M N) (hZ : Z ∈ 𝔤) :
    M*Z-Z*M ∈ 𝔤 := by
  let F := fun s : ℝ => exp (s • (-Z))*M*exp (s • Z)-M
  have hm (s : ℝ) : F s ∈ 𝔤 := by
    have hh := tangent_conjugate_difference G 𝔤 h
      (expUnit (s • Z)) (hexp _ (𝔤.smul_mem s hZ))
    simpa only [F, expUnit, Units.val_mk, Units.inv_mk, smul_neg] using hh
  have hd : HasDerivAt F (M*Z-Z*M) 0 := by
    convert (flow_derivative (-Z) Z M 0).sub_const M using 1
    rw [flow_initial]
    noncomm_ring
  exact derivative_mem_submodule 𝔤 hg hd hm

theorem right_error_derivative (X H : ℝ → Aˣ) {M N : A} {t : ℝ}
    (hX : HasDerivAt (fun s => (X s).val) (field M N (X t).val) t)
    (hH : HasDerivAt (fun s => (H s).val) (field M N (H t).val) t) :
    HasDerivAt (fun s => (X s*(H s)⁻¹).val)
      (M*(X t*(H t)⁻¹).val-(X t*(H t)⁻¹).val*M) t := by
  have h := Estimation.group_affine_right_error_derivative X H
    (field M N) (field_group_affine M N) hX (Δ := 0) (by simpa using hH)
  convert h using 1
  simp only [field, mul_one, one_mul, mul_add, mul_zero, sub_zero]
  noncomm_ring

theorem left_error_derivative (X H : ℝ → Aˣ) {M N : A} {t : ℝ}
    (hX : HasDerivAt (fun s => (X s).val) (field M N (X t).val) t)
    (hH : HasDerivAt (fun s => (H s).val) (field M N (H t).val) t) :
    HasDerivAt (fun s => ((X s)⁻¹*H s).val)
      (((X t)⁻¹*H t).val*N-N*((X t)⁻¹*H t).val) t := by
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (X t)).comp_hasDerivAt t hX
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hi
  convert hi.mul hH using 1
  simp only [field, Units.val_mul, add_mul, mul_add, neg_mul, mul_neg, mul_assoc,
    Units.mul_inv, mul_one]
  simp only [← mul_assoc, Units.inv_mul, one_mul]
  noncomm_ring

/-- The ambient commutator is a bounded linear operator, including when
its coefficient is not itself a Lie-algebra element. -/
def commutator (M : A) : A →L[ℝ] A :=
  ContinuousLinearMap.mul ℝ A M - (ContinuousLinearMap.mul ℝ A).flip M

@[simp] theorem commutator_apply (M Z : A) : commutator M Z = M*Z-Z*M := rfl

theorem conjugation_derivative (L : ℝ → Aˣ) {M Z : A} {t : ℝ}
    (hL : HasDerivAt (fun s => (L s).val) (M*(L t).val) t) :
    HasDerivAt (fun s => (L s).val*Z*((L s)⁻¹).val)
      (M*((L t).val*Z*((L t)⁻¹).val)-((L t).val*Z*((L t)⁻¹).val)*M) t := by
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (L t)).comp_hasDerivAt t hL
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hi
  convert (hL.mul_const Z).mul hi using 1
  simp only [mul_neg, neg_mul, mul_assoc, Units.mul_inv, mul_one]
  noncomm_ring

/-- Exact global exponential lift of the commutator error equation.
No small-error assumption, logarithm, constant input, or truncation is used.
The initial error must be an exponential; surjectivity is not presumed. -/
theorem exists_exact_loglinear_lift (M : ℝ → A) (hM : Continuous M)
    (E : ℝ → A) (hE : ∀ t, HasDerivAt E (M t*E t-E t*M t) t)
    (ξ₀ : A) (h₀ : E 0 = exp ξ₀) :
    ∃ ξ : ℝ → A, ξ 0 = ξ₀ ∧
      (∀ t, HasDerivAt ξ (commutator (M t) (ξ t)) t) ∧
      ∀ t, exp (ξ t) = E t := by
  obtain ⟨L,hL₀,hL⟩ := LinearODE.exists_unit_solution M hM
  let ξ := fun t => (L t).val*ξ₀*((L t)⁻¹).val
  have hd (t : ℝ) : HasDerivAt ξ (commutator (M t) (ξ t)) t :=
    conjugation_derivative L (hL t)
  have heq : E = fun t => (L t).val*exp ξ₀*((L t)⁻¹).val := by
    apply Magnus.mixed_flow_unique M (fun t => -M t) hM hM.neg
    · intro t; simpa only [mul_neg, ← sub_eq_add_neg] using hE t
    · intro t
      simpa only [mul_neg, ← sub_eq_add_neg] using
        conjugation_derivative L (Z := exp ξ₀) (hL t)
    · simpa [hL₀] using h₀
  refine ⟨ξ, by simp [ξ, hL₀], hd, ?_⟩
  intro t
  rw [heq]
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact exp_units_conj (L t) ξ₀

/-- Tangency closes the remaining geometric obligation: the exact
linear lift stays in the finite-dimensional Lie algebra for all time.
Existence is obtained by solving the restricted linear ODE in 𝔤. -/
theorem exists_exact_lie_lift (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A)
    [FiniteDimensional ℝ 𝔤] (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (M N : ℝ → A) (hM : Continuous M) (hT : ∀ t, TangentOn G 𝔤 (M t) (N t))
    (E : ℝ → A) (hE : ∀ t, HasDerivAt E (M t*E t-E t*M t) t)
    (ξ₀ : 𝔤) (h₀ : E 0 = exp (ξ₀ : A)) :
    ∃ ξ : ℝ → A, ξ 0 = (ξ₀ : A) ∧
      (∀ t, HasDerivAt ξ (commutator (M t) (ξ t)) t) ∧
      (∀ t, exp (ξ t) = E t) ∧ ∀ t, ξ t ∈ 𝔤 := by
  letI : CompleteSpace 𝔤 := FiniteDimensional.complete ℝ 𝔤
  let D : ℝ → 𝔤 →L[ℝ] 𝔤 := fun t =>
    ((commutator (M t)).comp 𝔤.subtypeL).codRestrict 𝔤
      (fun Z => tangent_commutator_mem G 𝔤 𝔤.closed_of_finiteDimensional
        hexp (hT t) Z.property)
  have hD : Continuous D := by
    apply continuous_clm_apply.mpr
    intro Z
    exact ((hM.mul continuous_const).sub (continuous_const.mul hM)).subtype_mk _
  obtain ⟨z,hz₀,hz⟩ := LinearODE.exists_solution D hD ξ₀
  let ξ : ℝ → A := fun t => (z t : A)
  have hd (t : ℝ) : HasDerivAt ξ (commutator (M t) (ξ t)) t :=
    𝔤.subtypeL.hasFDerivAt.comp_hasDerivAt t (hz t)
  obtain ⟨η,hη₀,hη,hηE⟩ := exists_exact_loglinear_lift M hM E hE ξ₀ h₀
  have heq : ξ = η := by
    apply Magnus.mixed_flow_unique M (fun t => -M t) hM hM.neg
    · intro t; simpa [commutator_apply, sub_eq_add_neg] using hd t
    · intro t; simpa [commutator_apply, sub_eq_add_neg] using hη t
    · simpa [ξ, hz₀] using hη₀.symm
  exact ⟨ξ, by simp [ξ, hz₀], hd, fun t => heq ▸ hηE t, fun t => (z t).property⟩

/-- Applies the exponential lift theorem to actual true/reference
trajectories with the same time-varying ambient M and N. -/
theorem mixed_trajectories_loglinear (M N : ℝ → A) (hM : Continuous M)
    (X H : ℝ → Aˣ)
    (hX : ∀ t, HasDerivAt (fun s => (X s).val) (field (M t) (N t) (X t).val) t)
    (hH : ∀ t, HasDerivAt (fun s => (H s).val) (field (M t) (N t) (H t).val) t)
    (ξ₀ : A) (h₀ : (X 0*(H 0)⁻¹).val = exp ξ₀) :
    ∃ ξ : ℝ → A, ξ 0 = ξ₀ ∧
      (∀ t, HasDerivAt ξ (commutator (M t) (ξ t)) t) ∧
      ∀ t, exp (ξ t) = (X t*(H t)⁻¹).val :=
  exists_exact_loglinear_lift M hM _
    (fun t => right_error_derivative X H (hX t) (hH t)) ξ₀ h₀

/-- A selected logarithm agrees with the lift wherever it is a left
inverse of exp. This condition excludes branch changes and cut loci. -/
theorem selected_log_eq (U : Set A) (logG : A → A)
    (hlog : ∀ Z ∈ U, logG (exp Z) = Z)
    (ξ E : ℝ → A) (he : ∀ t, exp (ξ t) = E t) {t : ℝ} (ht : ξ t ∈ U) :
    logG (E t) = ξ t := by rw [← he t]; exact hlog _ ht

theorem selected_log_derivative (U : Set A) (logG : A → A)
    (hlog : ∀ Z ∈ U, logG (exp Z) = Z)
    (ξ E : ℝ → A) (he : ∀ t, exp (ξ t) = E t) {t : ℝ} {v : A}
    (hU : ∀ᶠ s in 𝓝 t, ξ s ∈ U) (hξ : HasDerivAt ξ v t) :
    HasDerivAt (fun s => logG (E s)) v t := by
  apply hξ.congr_of_eventuallyEq
  filter_upwards [hU] with s hs
  exact selected_log_eq U logG hlog ξ E he hs

end GNC.MixedInvariant
