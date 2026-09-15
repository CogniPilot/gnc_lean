import GNC.Analysis.FundamentalSolution
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! State-transition tensors in a chosen vector-space error chart.

Derivatives here are with respect to the initial error, not time or uncertain
input parameters. A linear error transition has no tensors of order two and
above. Adding a nonlinear residual to a linear vector field makes its higher
derivatives exactly those of the residual. These facts do not assert that an
arbitrary nonlinear physical system admits a linear error chart.
-/
noncomputable section
open scoped NNReal
namespace GNC.StateTransitionTensor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every higher state tensor of a bounded linear transition vanishes. -/
theorem linear_higher (L : E →L[ℝ] F) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ (n+2) L x = 0 := by
  rw [show n+2=(n+1)+1 by omega]
  ext m
  rw [iteratedFDeriv_succ_apply_right]
  simp [ContinuousLinearMap.fderiv,iteratedFDeriv_succ_const]

/-- The higher derivatives of the vector field arise only from its
nonlinear residual. Smoothness is required at the derivative order used. -/
theorem residual_higher (L : E →L[ℝ] F) (r : E → F) (n : ℕ) (x : E)
    (hr : ContDiffAt ℝ (n+2) r x) :
    iteratedFDeriv ℝ (n+2) (fun y => L y+r y) x = iteratedFDeriv ℝ (n+2) r x := by
  rw [fun_iteratedFDeriv_add_apply L.contDiff.contDiffAt hr,linear_higher,zero_add]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Nonlinear physical reconstruction can preserve an algebra-space
certificate. Its distortion and both chart memberships must be supplied. -/
theorem reconstruction_bound (reconstruct : E → F) (U : Set E) (K : ℝ≥0)
    (hK : LipschitzOnWith K reconstruct U) {x y : E} (hx : x ∈ U) (hy : y ∈ U)
    {ε : ℝ} (h : ‖x-y‖≤ε) :
    ‖reconstruct x-reconstruct y‖≤(K:ℝ)*ε :=
  (hK.norm_sub_le hx hy).trans (mul_le_mul_of_nonneg_left h K.2)

section Flow
variable [CompleteSpace E]

/-- The exact transition of a continuous linear error ODE. This defines
a mathematical solution; computing it with Magnus still requires a time
integration or closed-form certificate. -/
def transition (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (t : ℝ) : E →L[ℝ] E :=
  (ForcedResponse.fundamental A hA t).val

theorem transition_initial (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) :
    transition A hA 0 x=x := by
  simp [transition,ForcedResponse.fundamental_initial]

theorem transition_derivative (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x : E) (t : ℝ) :
    HasDerivAt (fun s => transition A hA s x) (A t (transition A hA t x)) t := by
  exact (ContinuousLinearMap.apply ℝ E x).hasFDerivAt.comp_hasDerivAt t
    (ForcedResponse.fundamental_derivative A hA t)

/-- One STM describes the whole initial-error family, at every time.
No higher-order tensors have to be propagated for this linear equation. -/
theorem transition_higher (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (t : ℝ) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ (n+2) (transition A hA t) x=0 :=
  linear_higher _ n x

/-- Identification with any supplied solution, using ODE uniqueness. -/
theorem solution_eq_transition (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (f : ℝ → E) (hf : ∀ t, HasDerivAt f (A t (f t)) t) (t : ℝ) :
    f t=transition A hA t (f 0) := by
  have hu := ForcedResponse.exists_unique_response A hA (fun _ => 0) continuous_const (f 0)
  have he : f=(fun s => transition A hA s (f 0)) := hu.unique
    ⟨rfl,fun s => by simpa using hf s⟩
    ⟨transition_initial A hA _,fun s => by simpa using transition_derivative A hA (f 0) s⟩
  exact congrFun he t

end Flow
end GNC.StateTransitionTensor
