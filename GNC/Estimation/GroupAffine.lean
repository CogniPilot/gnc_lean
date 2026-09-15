import GNC.Analysis.FundamentalSolution
import Mathlib.Tactic

/-! Right-error dynamics on a group of units in a real Banach algebra.
This covers matrix-group calculations once tangency/subgroup preservation
has been established separately. It is not a construction of every
homogeneous-space EqF lift.
-/
noncomputable section
namespace GNC.Estimation
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Group affinity is required only on the state subgroup, not on every
invertible ambient matrix. Tangency is a separate geometric requirement. -/
def GroupAffineOn (G : Subgroup Aˣ) (f : A → A) : Prop := ∀ X ∈ G, ∀ Y ∈ G,
  f (X*Y).val = f X.val*Y.val+X.val*f Y.val-X.val*f 1*Y.val

def GroupAffine (f : A → A) : Prop := ∀ X Y : Aˣ,
  f (X*Y).val = f X.val*Y.val+X.val*f Y.val-X.val*f 1*Y.val

/-- The exact nonlinear derivative of true * estimated-inverse, including
an observer correction. No equivariance or group-affinity is assumed. -/
theorem right_error_derivative (X H : ℝ → Aˣ) (f : A → A) {Δ : A} {t : ℝ}
    (hX : HasDerivAt (fun s => (X s).val) (f (X t).val) t)
    (hH : HasDerivAt (fun s => (H s).val) (f (H t).val+Δ*(H t).val) t) :
    HasDerivAt (fun s => (X s*(H s)⁻¹).val)
      ((f (X t).val-(X t*(H t)⁻¹).val*f (H t).val)*((H t)⁻¹).val-
        (X t*(H t)⁻¹).val*Δ) t := by
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) (H t)).comp_hasDerivAt t hH
  simp only [Function.comp_def, Ring.inverse_unit, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] at hi
  convert hX.mul hi using 1
  simp only [Units.val_mul, add_mul, mul_add, neg_mul, mul_neg, sub_mul, mul_assoc,
    Units.mul_inv, mul_one]
  noncomm_ring

/-- Group affinity removes estimated-state dependence from the exact
pre-observer error vector field. This is the structural step used in the
IEKF specialization; the general log-linear theorem is a further result. -/
theorem group_affine_error (f : A → A) (hf : GroupAffine f) (X H : Aˣ) :
    (f X.val-(X*H⁻¹).val*f H.val)*(H⁻¹).val =
      f (X*H⁻¹).val-(X*H⁻¹).val*f 1 := by
  have h := hf (X*H⁻¹) H
  simp only [inv_mul_cancel_right] at h
  rw [h]
  simp only [sub_mul, add_mul, mul_assoc, Units.mul_inv, mul_one]
  noncomm_ring

theorem group_affine_on_error (G : Subgroup Aˣ) (f : A → A)
    (hf : GroupAffineOn G f) (X H : Aˣ) (hX : X ∈ G) (hH : H ∈ G) :
    (f X.val-(X*H⁻¹).val*f H.val)*(H⁻¹).val =
      f (X*H⁻¹).val-(X*H⁻¹).val*f 1 := by
  have h := hf (X*H⁻¹) (G.mul_mem hX (G.inv_mem hH)) H hH
  simp only [inv_mul_cancel_right] at h
  rw [h]
  simp only [sub_mul, add_mul, mul_assoc, Units.mul_inv, mul_one]
  noncomm_ring

theorem group_affine_on_right_error_derivative (G : Subgroup Aˣ)
    (X H : ℝ → Aˣ) (f : A → A) (hf : GroupAffineOn G f) {Δ : A} {t : ℝ}
    (hXG : X t ∈ G) (hHG : H t ∈ G)
    (hX : HasDerivAt (fun s => (X s).val) (f (X t).val) t)
    (hH : HasDerivAt (fun s => (H s).val) (f (H t).val+Δ*(H t).val) t) :
    HasDerivAt (fun s => (X s*(H s)⁻¹).val)
      (f (X t*(H t)⁻¹).val-(X t*(H t)⁻¹).val*f 1-(X t*(H t)⁻¹).val*Δ) t := by
  simpa only [group_affine_on_error G f hf (X t) (H t) hXG hHG] using
    right_error_derivative X H f hX hH

theorem group_affine_right_error_derivative (X H : ℝ → Aˣ)
    (f : A → A) (hf : GroupAffine f) {Δ : A} {t : ℝ}
    (hX : HasDerivAt (fun s => (X s).val) (f (X t).val) t)
    (hH : HasDerivAt (fun s => (H s).val) (f (H t).val+Δ*(H t).val) t) :
    HasDerivAt (fun s => (X s*(H s)⁻¹).val)
      (f (X t*(H t)⁻¹).val-(X t*(H t)⁻¹).val*f 1-(X t*(H t)⁻¹).val*Δ) t := by
  simpa only [group_affine_error f hf] using right_error_derivative X H f hX hH

end GNC.Estimation
