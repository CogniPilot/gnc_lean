import GNC.Dynamics.GroupAffineRigidity
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Trace

/-! When does a group-affine field admit state-independent ambient
coefficients? The exact test is first-order and linear in the unknown
matrix M. A basis suffices. Non-degenerate Killing form gives a sufficient
condition by reusing mathlib's theorem that derivations are inner.

The analytic input `hD` states the actual derivatives along exponential
curves. In the Killing corollary their group-error part is supplied as a
Lie derivation; the general manifold construction of that derivation is
not silently assumed to have been formalized here.
-/
noncomputable section
open NormedSpace Set
namespace GNC.MixedClassification
open MixedInvariant Estimation
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The candidate linear error generator in the given representation. -/
def implementedMap (𝔤 : Submodule ℝ A) (M : A) : 𝔤 →ₗ[ℝ] A :=
  (commutator M).toLinearMap.comp 𝔤.subtype

@[simp] theorem implementedMap_apply (𝔤 : Submodule ℝ A) (M : A) (Z : 𝔤) :
    implementedMap 𝔤 M Z = M*(Z:A)-(Z:A)*M := rfl

def implementationLinear (𝔤 : Submodule ℝ A) : A →ₗ[ℝ] (𝔤 →ₗ[ℝ] A) where
  toFun := implementedMap 𝔤
  map_add' M N := by
    ext Z
    simp only [implementedMap_apply, LinearMap.add_apply, add_mul, mul_add]
    abel
  map_smul' r M := by
    ext Z
    simp only [implementedMap_apply, LinearMap.smul_apply, smul_mul_assoc,
      mul_smul_comm, smul_sub, RingHom.id_apply]

/-- One finite family of certificates covers every prescribed linear
combination of its generators, including time-varying input coefficients. -/
theorem implemented_family {ι : Type*} [Fintype ι] (𝔤 : Submodule ℝ A)
    (D : ι → 𝔤 →ₗ[ℝ] A) (M : ι → A) (u : ι → ℝ)
    (h : ∀ i, D i = implementedMap 𝔤 (M i)) :
    ∑ i, u i • D i = implementedMap 𝔤 (∑ i, u i • M i) := by
  change _ = implementationLinear 𝔤 (∑ i, u i • M i)
  rw [map_sum]
  simp only [map_smul, h]
  rfl

/-- Necessary and sufficient condition for a specified M. N is forced
to be f(I)-M by evaluating the vector field at the identity. -/
theorem representation_iff_generator (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A)
    (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (hgen : G ≤ Subgroup.closure {X : Aˣ | ∃ Z ∈ 𝔤, expUnit Z = X})
    (f : A → A) (hf : GroupAffineOn G f) (D : 𝔤 →ₗ[ℝ] A)
    (hD : ∀ Z : 𝔤, HasDerivAt (fun s : ℝ => f (exp (s • (Z:A))))
      (D Z+(Z:A)*f 1) 0) (M : A) :
    (∀ X ∈ G, f X.val = field M (f 1-M) X.val) ↔ D = implementedMap 𝔤 M := by
  rw [mixed_representation_iff_first_jet G 𝔤 hexp hgen f hf M (f 1-M)]
  constructor
  · rintro ⟨_,hd⟩
    ext Z
    have he := (hD Z).unique (hd Z Z.property)
    change D Z = M*(Z:A)-(Z:A)*M
    linear_combination (norm := noncomm_ring) he
  · intro he
    refine ⟨by abel, ?_⟩
    intro Z hZ
    convert hD ⟨Z,hZ⟩ using 1
    rw [he]
    simp only [implementedMap_apply]
    noncomm_ring

/-- An arbitrary nonlinear functional identity is reduced to existence
of one solution of a linear equation between linear maps. -/
theorem exists_representation_iff (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A)
    (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (hgen : G ≤ Subgroup.closure {X : Aˣ | ∃ Z ∈ 𝔤, expUnit Z = X})
    (f : A → A) (hf : GroupAffineOn G f) (D : 𝔤 →ₗ[ℝ] A)
    (hD : ∀ Z : 𝔤, HasDerivAt (fun s : ℝ => f (exp (s • (Z:A))))
      (D Z+(Z:A)*f 1) 0) :
    (∃ M N : A, ∀ X ∈ G, f X.val = field M N X.val) ↔
      ∃ M : A, D = implementedMap 𝔤 M := by
  constructor
  · rintro ⟨M,N,hMN⟩
    have h₀ : f 1 = M+N := by simpa [field] using hMN 1 G.one_mem
    refine ⟨M,(representation_iff_generator G 𝔤 hexp hgen f hf D hD M).mp ?_⟩
    simpa [h₀] using hMN
  · rintro ⟨M,hM⟩
    exact ⟨M,f 1-M,(representation_iff_generator G 𝔤 hexp hgen f hf D hD M).mpr hM⟩

/-- The concise system-level equivalence: an implementable first
derivative is a restriction on the candidate field, without presuming
group affinity. Under this restriction group affinity is equivalent to
the mixed form. The reverse implication requires no derivative argument. -/
theorem group_affine_iff_mixed_of_implemented_generator
    (G : Subgroup Aˣ) (𝔤 : Submodule ℝ A)
    (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (hgen : G ≤ Subgroup.closure {X : Aˣ | ∃ Z ∈ 𝔤, expUnit Z = X})
    (f : A → A) (D : 𝔤 →ₗ[ℝ] A)
    (hD : ∀ Z : 𝔤, HasDerivAt (fun s : ℝ => f (exp (s • (Z:A))))
      (D Z+(Z:A)*f 1) 0)
    (himpl : ∃ M : A, D = implementedMap 𝔤 M) :
    GroupAffineOn G f ↔ ∃ M N : A, ∀ X ∈ G, f X.val = field M N X.val := by
  constructor
  · intro hf
    exact (exists_representation_iff G 𝔤 hexp hgen f hf D hD).mpr himpl
  · rintro ⟨M,N,hMN⟩ X hX Y hY
    rw [hMN (X*Y) (G.mul_mem hX hY), hMN X hX, hMN Y hY,
      show f 1 = field M N 1 by simpa using hMN 1 G.one_mem]
    exact field_group_affine_on G M N X hX Y hY

/-- In finite dimension it suffices to check one matrix equation per
basis vector. No test over the nonlinear state manifold is left. -/
theorem implemented_iff_basis {ι : Type*} (𝔤 : Submodule ℝ A)
    (b : Module.Basis ι ℝ 𝔤) (D : 𝔤 →ₗ[ℝ] A) (M : A) :
    D = implementedMap 𝔤 M ↔ ∀ i, D (b i) = M*(b i:A)-(b i:A)*M := by
  constructor
  · intro h i; rw [h]; rfl
  · intro h; exact b.ext h

/-- Different implementing matrices differ by an element commuting
with every represented Lie-algebra direction. -/
theorem implementation_nonuniqueness (𝔤 : Submodule ℝ A) (M P : A) :
    implementedMap 𝔤 M = implementedMap 𝔤 P ↔
      ∀ Z : 𝔤, (M-P)*(Z:A) = (Z:A)*(M-P) := by
  constructor
  · intro h Z
    have he := LinearMap.congr_fun h Z
    simp only [implementedMap_apply] at he
    linear_combination (norm := noncomm_ring) he
  · intro h
    ext Z
    change M*(Z:A)-(Z:A)*M = P*(Z:A)-(Z:A)*P
    linear_combination (norm := noncomm_ring) h Z

/-- A genuinely constant ambient vector field is a different condition
from a field with constant left/right generators. Even the constant
field still has to satisfy this group-affinity test. -/
theorem constant_group_affine_iff (G : Subgroup Aˣ) (C : A) :
    GroupAffineOn G (fun _ => C) ↔
      ∀ X ∈ G, ∀ Y ∈ G, (X.val-1)*C*(Y.val-1) = 0 := by
  constructor
  · intro h X hX Y hY
    have he := h X hX Y hY
    dsimp only at he
    linear_combination (norm := noncomm_ring) he
  · intro h X hX Y hY
    dsimp only
    linear_combination (norm := noncomm_ring) h X hX Y hY

/-- Semisimple-type sufficient condition: mathlib supplies innerness
from the non-degenerate Killing form. The derivative hypotheses connect
this algebraic result to the actual group-affine vector field. -/
theorem exists_representation_of_killing (G : Subgroup Aˣ) (𝔤 : LieSubalgebra ℝ A)
    [FiniteDimensional ℝ 𝔤] [LieAlgebra.IsKilling ℝ 𝔤]
    (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (hgen : G ≤ Subgroup.closure {X : Aˣ | ∃ Z ∈ 𝔤, expUnit Z = X})
    (f : A → A) (hf : GroupAffineOn G f) (hb : f 1 ∈ 𝔤)
    (D : LieDerivation ℝ 𝔤 𝔤)
    (hD : ∀ Z : 𝔤, HasDerivAt (fun s : ℝ => f (exp (s • (Z:A))))
      ((D Z:A)+(Z:A)*f 1) 0) :
    ∃ M N : A, M ∈ 𝔤 ∧ N ∈ 𝔤 ∧ ∀ X ∈ G, f X.val = field M N X.val := by
  obtain ⟨m,hm⟩ := LieDerivation.IsKilling.exists_eq_ad D
  let D' : 𝔤 →ₗ[ℝ] A := 𝔤.toSubmodule.subtype.comp D.toLinearMap
  have hM : D' = implementedMap 𝔤.toSubmodule (m:A) := by
    ext Z
    have hl : LieAlgebra.ad ℝ 𝔤 m = D.toLinearMap := by
      simpa using congrArg (fun T : LieDerivation ℝ 𝔤 𝔤 => T.toLinearMap) hm
    have he := congrArg (fun z : 𝔤 => (z:A)) (LinearMap.congr_fun hl Z)
    simpa [D', LieSubalgebra.coe_bracket, Ring.lie_def] using he.symm
  refine ⟨m,f 1-(m:A),m.property,𝔤.sub_mem hb m.property,?_⟩
  exact (representation_iff_generator G 𝔤.toSubmodule hexp hgen f hf D' hD m).mpr hM

end GNC.MixedClassification

namespace GNC.MixedClassification
section LieRepresentation
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Changing to the adjoint representation implements every derivation
as an ambient commutator. Mathlib supplies the central identity. This
lemma alone does not assert faithfulness of a global group embedding. -/
theorem adjoint_implementation (D : LieDerivation R L L) (Z : L) :
    LieAlgebra.ad R L (D Z) =
      D.toLinearMap * LieAlgebra.ad R L Z - LieAlgebra.ad R L Z * D.toLinearMap := by
  ext W
  change ⁅D Z,W⁆ = D ⁅Z,W⁆-⁅Z,D W⁆
  rw [D.apply_lie_eq_add]
  abel

end LieRepresentation

/-- A cheap obstruction test: an implemented generator has trace zero
on every represented direction, by mathlib's trace-of-product identity. -/
theorem implemented_trace_zero {n : Type*} [Fintype n] [DecidableEq n]
    (M Z : Matrix n n ℝ) : Matrix.trace (M*Z-Z*M) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

end GNC.MixedClassification
