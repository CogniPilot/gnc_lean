import GNC.Control.Lyapunov
import GNC.Analysis.LinearODE
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact three-integrator backstepping for the flat-output aircraft outer
loop. The allocation theorem explicitly requires a nonsingular decoupling map.
-/
noncomputable section
namespace GNC.FlatBackstepping
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def e₂ (k₁ : ℝ) (p v : E) : E := v + k₁ • p
def e₃ (k₁ k₂ : ℝ) (p v a : E) : E :=
  a + (1:ℝ) • p + k₁ • v + k₂ • e₂ k₁ p v

/-- The desired third derivative of position error, obtained by differentiating
the two virtual controls. It depends only on current p, v, a. -/
def jerk (k₁ k₂ k₃ : ℝ) (p v a : E) : E :=
  -e₂ k₁ p v - k₃ • e₃ k₁ k₂ p v a -
    v - k₁ • a - k₂ • (a + k₁ • v)

theorem first_stage (k₁ : ℝ) (p v : E) :
    v = -k₁ • p + e₂ k₁ p v := by
  simp [e₂, neg_smul]

theorem second_stage (k₁ k₂ : ℝ) (p v a : E) :
    a + k₁ • v = -p - k₂ • e₂ k₁ p v + e₃ k₁ k₂ p v a := by
  simp [e₃]; abel

theorem third_stage (k₁ k₂ k₃ : ℝ) (p v a : E) :
    jerk k₁ k₂ k₃ p v a + v + k₁ • a + k₂ • (a + k₁ • v) =
      -e₂ k₁ p v - k₃ • e₃ k₁ k₂ p v a := by
  unfold jerk; abel

theorem jerk_expanded (k₁ k₂ k₃ : ℝ) (p v a : E) :
    jerk k₁ k₂ k₃ p v a =
      -(k₁+k₃+k₁*k₂*k₃) • p -
      (2+k₁*k₂+k₁*k₃+k₂*k₃) • v -
      (k₁+k₂+k₃) • a := by
  dsimp [jerk, e₃, e₂]
  module

theorem coordinates_reconstruct (k₁ k₂ : ℝ) (p v a : E) :
    v = e₂ k₁ p v-k₁ • p ∧
    a = e₃ k₁ k₂ p v a-p-k₁ • v-k₂ • e₂ k₁ p v := by
  constructor <;> simp [e₂, e₃] <;> module

theorem e₂_derivative {p v a : ℝ → E} {k₁ t : ℝ}
    (hp : HasDerivAt p (v t) t) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => e₂ k₁ (p s) (v s)) (a t+k₁ • v t) t :=
  hv.add (hp.const_smul k₁)

theorem e₃_derivative {p v a : ℝ → E} {j : E} {k₁ k₂ t : ℝ}
    (hp : HasDerivAt p (v t) t) (hv : HasDerivAt v (a t) t)
    (ha : HasDerivAt a j t) :
    HasDerivAt (fun s => e₃ k₁ k₂ (p s) (v s) (a s))
      (j+v t+k₁ • a t+k₂ • (a t+k₁ • v t)) t := by
  simpa only [e₃, one_smul] using
    ((ha.add hp).add (hv.const_smul k₁)).add
      ((e₂_derivative (k₁ := k₁) hp hv).const_smul k₂)

/-- The actual third-order error ODE realizes the backstepping cascade, and
its energy decays. No target-cascade equation is supplied as a hypothesis. -/
theorem tracking_energy_bound {p v a : ℝ → E} {k₁ k₂ k₃ k t₀ T : ℝ}
    (hk₁ : k ≤ k₁) (hk₂ : k ≤ k₂) (hk₃ : k ≤ k₃)
    (hp : ∀ t, HasDerivAt p (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (ha : ∀ t, HasDerivAt a (jerk k₁ k₂ k₃ (p t) (v t) (a t)) t) :
    ∀ t ∈ Set.Icc t₀ T,
      Lyapunov.energy (p t) (e₂ k₁ (p t) (v t)) (e₃ k₁ k₂ (p t) (v t) (a t)) ≤
      Lyapunov.energy (p t₀) (e₂ k₁ (p t₀) (v t₀)) (e₃ k₁ k₂ (p t₀) (v t₀) (a t₀)) *
        Real.exp (-2*k*(t-t₀)) := by
  apply Lyapunov.backstepping_exponential
    (S := fun _ => 0) (B := fun _ => ContinuousLinearMap.id ℝ E)
    (Bt := fun _ => ContinuousLinearMap.id ℝ E) hk₁ hk₂ hk₃
  · simp
  · intro t x y; simpa using (real_inner_comm x y).symm
  · intro t
    simpa only [ContinuousLinearMap.zero_apply, zero_sub, ← neg_smul,
      ← first_stage] using hp t
  · intro t
    convert e₂_derivative (k₁ := k₁) (hp t) (hv t) using 1
    simp only [ContinuousLinearMap.zero_apply, zero_sub, ContinuousLinearMap.id_apply]
    exact (second_stage _ _ _ _ _).symm
  · intro t
    convert e₃_derivative (k₁ := k₁) (k₂ := k₂) (hp t) (hv t) (ha t) using 1
    simp only [ContinuousLinearMap.zero_apply, zero_sub, ContinuousLinearMap.id_apply]
    exact (third_stage _ _ _ _ _ _).symm

/-- Lévine Eq. (14.9) abstractly: four flat-output derivatives are affine in
four virtual inputs. An invertible decoupling map realizes the requested output.
Its nonsingularity and physical actuator feasibility must be established by
the chosen aircraft model; this theorem does not assume arbitrary forces. -/
theorem affine_allocation {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : F ≃ₗ[ℝ] F) (drift target : F) :
    drift + D (D.symm (target-drift)) = target := by
  simp

end GNC.FlatBackstepping
