import GNC.Dynamics.MixedLogLinear
import GNC.Analysis.StateTransitionTensor

/-! Initial-error STTs for the actual mixed-invariant error equation.

The exponential lift is exact for matched prescribed inputs. A chosen
principal logarithm agrees with this lift only on its chart. Uncertain
input parameters are not included in the differentiation variable.
-/
noncomputable section
namespace GNC.MixedInvariant
open NormedSpace
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

omit [CompleteSpace B] in
theorem continuous_commutator (M : ℝ → B) (hM : Continuous M) :
    Continuous (fun t => commutator (M t)) :=
  ((ContinuousLinearMap.mul ℝ B).continuous.comp hM).sub
    ((ContinuousLinearMap.mul ℝ B).flip.continuous.comp hM)

/-- One bounded linear transition for all initial errors. -/
def errorTransition (M : ℝ → B) (hM : Continuous M) (t : ℝ) : B →L[ℝ] B :=
  StateTransitionTensor.transition (fun s => commutator (M s))
    (continuous_commutator M hM) t

/-- The zero higher tensors belong to the lift, not the reconstructed
matrix entries. This holds for arbitrary continuous time variation in M. -/
theorem errorTransition_higher (M : ℝ → B) (hM : Continuous M)
    (t : ℝ) (n : ℕ) (Z : B) :
    iteratedFDeriv ℝ (n+2) (errorTransition M hM t) Z=0 :=
  StateTransitionTensor.linear_higher _ n Z

/-- Identification with the actual nonlinear error trajectory. -/
theorem errorTransition_reconstruction (M : ℝ → B) (hM : Continuous M)
    (E : ℝ → B) (hE : ∀ t, HasDerivAt E (M t*E t-E t*M t) t)
    (Z : B) (h₀ : E 0=exp Z) (t : ℝ) :
    exp (errorTransition M hM t Z)=E t := by
  obtain ⟨ξ,hξ₀,hξ,hξE⟩ := exists_exact_loglinear_lift M hM E hE Z h₀
  have he := StateTransitionTensor.solution_eq_transition
    (fun s => commutator (M s)) (continuous_commutator M hM) ξ hξ t
  rw [hξ₀] at he
  change exp (StateTransitionTensor.transition _ _ t Z)=E t
  rw [←he]
  exact hξE t

/-- Applying the tensor result to matched true/reference trajectories
requires no extra approximation of their initial exponential error. -/
theorem mixed_trajectory_reconstruction (M N : ℝ → B) (hM : Continuous M)
    (X H : ℝ → Bˣ)
    (hX : ∀ t, HasDerivAt (fun s => (X s).val) (field (M t) (N t) (X t).val) t)
    (hH : ∀ t, HasDerivAt (fun s => (H s).val) (field (M t) (N t) (H t).val) t)
    (Z : B) (h₀ : (X 0*(H 0)⁻¹).val=exp Z) (t : ℝ) :
    exp (errorTransition M hM t Z)=(X t*(H t)⁻¹).val :=
  errorTransition_reconstruction M hM _
    (fun s => right_error_derivative X H (hX s) (hH s)) Z h₀ t

/-- Tangency restricts the ambient transition to the actual Lie algebra. -/
theorem errorTransition_mem (G : Subgroup Bˣ) (𝔤 : Submodule ℝ B)
    [FiniteDimensional ℝ 𝔤] (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (M N : ℝ → B) (hM : Continuous M) (hT : ∀ t, TangentOn G 𝔤 (M t) (N t))
    (Z : 𝔤) (t : ℝ) : errorTransition M hM t Z ∈ 𝔤 := by
  obtain ⟨L,hL₀,hL⟩ := LinearODE.exists_unit_solution M hM
  let E := fun s => (L s).val*exp (Z : B)*((L s)⁻¹).val
  obtain ⟨ξ,hξ₀,hξ,_,hξmem⟩ := exists_exact_lie_lift G 𝔤 hexp M N hM hT E
    (fun s => conjugation_derivative L (Z := exp (Z : B)) (hL s))
    Z (by simp [E,hL₀])
  have he := StateTransitionTensor.solution_eq_transition
    (fun s => commutator (M s)) (continuous_commutator M hM) ξ hξ t
  rw [hξ₀] at he
  change StateTransitionTensor.transition _ _ t (Z : B) ∈ 𝔤
  rw [←he]
  exact hξmem t

def lieErrorTransition (G : Subgroup Bˣ) (𝔤 : Submodule ℝ B)
    [FiniteDimensional ℝ 𝔤] (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (M N : ℝ → B) (hM : Continuous M) (hT : ∀ t, TangentOn G 𝔤 (M t) (N t))
    (t : ℝ) : 𝔤 →L[ℝ] 𝔤 :=
  ((errorTransition M hM t).comp 𝔤.subtypeL).codRestrict 𝔤
    (fun Z => errorTransition_mem G 𝔤 hexp M N hM hT Z t)

/-- Vanishing higher tensors in the Lie algebra itself. -/
theorem lieErrorTransition_higher (G : Subgroup Bˣ) (𝔤 : Submodule ℝ B)
    [FiniteDimensional ℝ 𝔤] (hexp : ∀ Z ∈ 𝔤, expUnit Z ∈ G)
    (M N : ℝ → B) (hM : Continuous M) (hT : ∀ t, TangentOn G 𝔤 (M t) (N t))
    (t : ℝ) (n : ℕ) (Z : 𝔤) :
    iteratedFDeriv ℝ (n+2) (lieErrorTransition G 𝔤 hexp M N hM hT t) Z=0 :=
  StateTransitionTensor.linear_higher _ n Z

end GNC.MixedInvariant
